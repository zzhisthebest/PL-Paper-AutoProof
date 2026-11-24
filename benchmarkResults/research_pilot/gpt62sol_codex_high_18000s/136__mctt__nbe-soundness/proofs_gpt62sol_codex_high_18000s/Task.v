From Stdlib Require Import List Arith.PeanoNat Lia.
From Mctt.Core Require Import Base.
From Mctt.Core.Semantic Require Export NbE.

Import Domain_Notations.

Module SoundnessSupport.

(* The semantic model establishes evaluation, readback, and their compatibility
   with McTT typing and conversion. *)

Lemma fst_unique : forall m x y, eval_fst m x -> eval_fst m y -> x = y.
Proof. intros m x y H H'; destruct H; inversion H'; reflexivity. Qed.

Ltac use_induction_equalities :=
  repeat match goal with
  | H : forall y, ?P y -> ?x = y, H' : ?P ?z |- _ =>
      first [constr_eq x z; fail 1 | specialize (H z H'); subst z]
  | H : eval_fst ?m ?x, H' : eval_fst ?m ?y |- _ =>
      first [constr_eq H H'; fail 1
            | constr_eq x y; clear H'
            | let E := fresh in pose proof (fst_unique _ _ _ H H') as E; subst y]
  end.

Lemma evaluation_unique :
  (forall M ρ m, eval_exp M ρ m -> forall n, eval_exp M ρ n -> m = n) /\
  (forall A Z S m ρ x, eval_natrec A Z S m ρ x ->
     forall y, eval_natrec A Z S m ρ y -> x = y) /\
  (forall m n x, eval_app m n x -> forall y, eval_app m n y -> x = y) /\
  (forall m x, eval_snd m x -> forall y, eval_snd m y -> x = y) /\
  (forall a B BR m1 m2 n ρ x, eval_eqrec a B BR m1 m2 n ρ x ->
     forall y, eval_eqrec a B BR m1 m2 n ρ y -> x = y) /\
  (forall σ ρ ρ', eval_sub σ ρ ρ' -> forall ρ'', eval_sub σ ρ ρ'' -> ρ' = ρ'').
Proof.
  apply eval_mut_ind; intros;
    match goal with H : _ |- _ => inversion H; subst end;
    use_induction_equalities; reflexivity.
Qed.

Definition exp_unique := proj1 evaluation_unique.
Definition app_unique := proj1 (proj2 (proj2 evaluation_unique)).
Definition snd_unique := proj1 (proj2 (proj2 (proj2 evaluation_unique))).
Definition sub_unique := proj2 (proj2 (proj2 (proj2 (proj2 evaluation_unique)))).

Ltac resolve_eval :=
  repeat match goal with
  | H : eval_exp ?M ?ρ ?a, H' : eval_exp ?M ?ρ ?b |- _ =>
      first [constr_eq H H'; fail 1 | constr_eq a b; clear H'
            | let E := fresh in pose proof (exp_unique _ _ _ H _ H') as E; subst b]
  | H : eval_app ?m ?n ?a, H' : eval_app ?m ?n ?b |- _ =>
      first [constr_eq H H'; fail 1 | constr_eq a b; clear H'
            | let E := fresh in pose proof (app_unique _ _ _ H _ H') as E; subst b]
  | H : eval_snd ?m ?a, H' : eval_snd ?m ?b |- _ =>
      first [constr_eq H H'; fail 1 | constr_eq a b; clear H'
            | let E := fresh in pose proof (snd_unique _ _ H _ H') as E; subst b]
  | H : eval_sub ?σ ?ρ ?a, H' : eval_sub ?σ ?ρ ?b |- _ =>
      first [constr_eq H H'; fail 1 | constr_eq a b; clear H'
            | let E := fresh in pose proof (sub_unique _ _ _ H _ H') as E; subst b]
  end.

Lemma readback_unique :
  (forall s d W, read_nf s d W -> forall W', read_nf s d W' -> W = W') /\
  (forall s d W, read_ne s d W -> forall W', read_ne s d W' -> W = W') /\
  (forall s d W, read_typ s d W -> forall W', read_typ s d W' -> W = W').
Proof.
  apply read_mut_ind; intros;
    match goal with H : _ |- _ => inversion H; subst end;
    use_induction_equalities; resolve_eval; use_induction_equalities; reflexivity.
Qed.

Definition read_ne_unique := proj1 (proj2 readback_unique).

Lemma initial_env_unique : forall Γ ρ,
    initial_env Γ ρ -> forall ρ', initial_env Γ ρ' -> ρ = ρ'.
Proof.
  intros Γ ρ H; induction H; intros ρ' H'; inversion H'; subst;
    use_induction_equalities; resolve_eval; reflexivity.
Qed.

Lemma nbe_unique : forall Γ M A W W',
    nbe Γ M A W -> nbe Γ M A W' -> W = W'.
Proof.
  intros Γ M A W W' H H'; destruct H; inversion H'; subst.
  match goal with
  | H : initial_env ?Γ ?ρ, H' : initial_env ?Γ ?ρ' |- _ =>
      first [constr_eq H H'; fail 1
            | pose proof (initial_env_unique _ _ H _ H'); subst ρ']
  end.
  resolve_eval.
  eapply (proj1 readback_unique); eassumption.
Qed.

Definition relation := domain -> domain -> Prop.
Definition equivalent (R T : relation) := forall x y, R x y <-> T x y.
Definition includes (R T : relation) := forall x y, R x y -> T x y.
Definition partial_equivalence (R : relation) :=
  (forall x y, R x y -> R y x) /\
  (forall x y z, R x y -> R y z -> R x z).

Lemma equiv_refl : forall R, equivalent R R.
Proof. unfold equivalent; tauto. Qed.
Lemma equiv_sym : forall R T, equivalent R T -> equivalent T R.
Proof. unfold equivalent; intros; symmetry; auto. Qed.
Lemma equiv_trans : forall R S T, equivalent R S -> equivalent S T -> equivalent R T.
Proof. unfold equivalent; intros; etransitivity; eauto. Qed.
Lemma per_left : forall R, partial_equivalence R -> forall x y, R x y -> R x x.
Proof. intros R [HS HT] x y H; eauto. Qed.
Lemma per_right : forall R, partial_equivalence R -> forall x y, R x y -> R y y.
Proof. intros R [HS HT] x y H; eauto. Qed.
Lemma per_equiv : forall R T, equivalent R T -> partial_equivalence R -> partial_equivalence T.
Proof.
  intros R T HE [HS HT]; split.
  - intros x y H. apply HE, HS, HE, H.
  - intros x y z Hxy Hyz. apply HE. exact (HT _ _ _ (proj2 (HE _ _) Hxy) (proj2 (HE _ _) Hyz)).
Qed.

Definition ne_related n n' := forall s, exists N, read_ne s n N /\ read_ne s n' N.
Definition type_readback a a' := forall s, exists A, read_typ s a A /\ read_typ s a' A.
Definition term_readback a a' (R : relation) :=
  forall m m', R m m' -> forall s, exists M, read_nf s (d_dom a m) M /\ read_nf s (d_dom a' m') M.
Definition reflect_neutral a a' (R : relation) :=
  forall n n', ne_related n n' -> R (d_neut a n) (d_neut a' n').

Lemma ne_related_sym : forall n n', ne_related n n' -> ne_related n' n.
Proof. intros n n' H s; destruct (H s) as [N [? ?]]; eauto. Qed.
Lemma ne_related_trans : forall x y z, ne_related x y -> ne_related y z -> ne_related x z.
Proof.
  intros x y z Hxy Hyz s.
  destruct (Hxy s) as [M [HX HY]]. destruct (Hyz s) as [N [HY' HZ]].
  pose proof (read_ne_unique _ _ _ HY _ HY') as <-. eauto.
Qed.
Lemma ne_related_var : forall x, ne_related (d_var x) (d_var x).
Proof. intros x s; eexists; split; apply read_ne_var. Qed.
Lemma ne_related_app : forall a a' R m m' n n',
    term_readback a a' R -> ne_related m m' -> R n n' ->
    ne_related (d_app m (d_dom a n)) (d_app m' (d_dom a' n')).
Proof.
  intros a a' R m m' n n' HQ Hm Hn s.
  destruct (Hm s) as [M [? ?]]. destruct (HQ _ _ Hn s) as [N [? ?]].
  exists (ne_app M N); split; now apply read_ne_app.
Qed.
Lemma ne_related_fst : forall x y, ne_related x y -> ne_related (d_fst x) (d_fst y).
Proof. intros x y H s; destruct (H s) as [W [? ?]]; exists (ne_fst W); split; now constructor. Qed.
Lemma ne_related_snd : forall x y, ne_related x y -> ne_related (d_snd x) (d_snd y).
Proof. intros x y H s; destruct (H s) as [W [? ?]]; exists (ne_snd W); split; now constructor. Qed.

Inductive nat_rel : relation :=
| nat_rel_zero : nat_rel d_zero d_zero
| nat_rel_succ : forall m m', nat_rel m m' -> nat_rel (d_succ m) (d_succ m')
| nat_rel_neut : forall a a' n n', ne_related n n' -> nat_rel (d_neut a n) (d_neut a' n').

Definition opaque_rel : relation :=
  fun x y => exists a a' n n', x = d_neut a n /\ y = d_neut a' n' /\ ne_related n n'.

Definition pi_rel (R : relation) (T : domain -> domain -> relation) : relation :=
  fun f f' => forall x x', R x x' ->
    exists y y', eval_app f x y /\ eval_app f' x' y' /\ T x x' y y'.

Definition sigma_rel (R : relation) (T : domain -> domain -> relation) : relation :=
  fun p p' => exists x x' y y',
    eval_fst p x /\ eval_fst p' x' /\ eval_snd p y /\ eval_snd p' y' /\
    R x x' /\ T x x' y y'.

Inductive eq_rel (R : relation) (x y x' y' : domain) : relation :=
| eq_rel_refl : forall z z', R z z' -> R z x' -> R z y' -> R x z' -> R y z' ->
    eq_rel R x y x' y' (d_refl z) (d_refl z')
| eq_rel_neut : forall a a' n n', ne_related n n' ->
    eq_rel R x y x' y' (d_neut a n) (d_neut a' n').

Definition closures (R : relation) ρ B ρ' B' :=
  forall x x', R x x' -> exists b b', eval_exp B (extend_env ρ x) b /\ eval_exp B' (extend_env ρ' x') b'.

Inductive model_type (U : list relation) : domain -> domain -> relation -> Prop :=
| model_univ : forall i R, nth_error U i = Some R -> model_type U (d_univ i) (d_univ i) R
| model_nat : model_type U d_nat d_nat nat_rel
| model_opaque : forall a a' n n', ne_related n n' ->
    model_type U (d_neut a n) (d_neut a' n') opaque_rel
| model_pi : forall a a' ρ B ρ' B' R T,
    model_type U a a' R -> closures R ρ B ρ' B' ->
    (forall x x', R x x' -> forall b b',
      eval_exp B (extend_env ρ x) b -> eval_exp B' (extend_env ρ' x') b' -> model_type U b b' (T x x')) ->
    model_type U (d_pi a ρ B) (d_pi a' ρ' B') (pi_rel R T)
| model_sigma : forall a a' ρ B ρ' B' R T,
    model_type U a a' R -> closures R ρ B ρ' B' ->
    (forall x x', R x x' -> forall b b',
      eval_exp B (extend_env ρ x) b -> eval_exp B' (extend_env ρ' x') b' -> model_type U b b' (T x x')) ->
    model_type U (d_sigma a ρ B) (d_sigma a' ρ' B') (sigma_rel R T)
| model_eq : forall a a' x y x' y' R,
    model_type U a a' R -> R x x' -> R y y' ->
    model_type U (d_eq a x y) (d_eq a' x' y') (eq_rel R x y x' y')
| model_ext : forall a a' R T,
    model_type U a a' R -> equivalent R T -> model_type U a a' T.

Definition model_codomains U R ρ B ρ' B' T :=
  forall x x', R x x' -> forall b b',
    eval_exp B (extend_env ρ x) b -> eval_exp B' (extend_env ρ' x') b' -> model_type U b b' (T x x').

Definition universe_model U :=
  forall i R, nth_error U i = Some R ->
    (forall a a', R a a' -> type_readback a a') /\
    (forall a a', reflect_neutral a a' R).

Lemma nat_rel_readback : term_readback d_nat d_nat nat_rel.
Proof.
  intros m m' H; induction H; intros s.
  - exists nf_zero; split; constructor.
  - destruct (IHnat_rel s) as [W [? ?]]. exists (nf_succ W); split; now constructor.
  - destruct (H s) as [W [? ?]]. exists (nf_neut W); split; now constructor.
Qed.

Lemma model_readback : forall U, universe_model U ->
    forall a a' R, model_type U a a' R ->
      type_readback a a' /\ term_readback a a' R /\ reflect_neutral a a' R.
Proof.
  intros U HU a a' R H; induction H.
  - destruct (HU _ _ H) as [HQ HR]; split; [| split].
    + intros s; exists (nf_typ i); split; constructor.
    + intros b b' Hb s; destruct (HQ _ _ Hb s) as [N [? ?]]; exists N; split; now constructor.
    + apply HR.
  - split; [| split].
    + intros s; exists nf_nat; split; constructor.
    + exact nat_rel_readback.
    + intros n n' Hn; now constructor.
  - split; [| split].
    + intros s; destruct (H s) as [N [? ?]]; exists (nf_neut N); split; now constructor.
    + intros x y (b & b' & m & m' & -> & -> & Hm) s.
      destruct (Hm s) as [M [? ?]]; exists (nf_neut M); split; now apply read_nf_neut.
    + intros m m' Hm; exists (d_neut a n), (d_neut a' n'), m, m'; repeat split; exact Hm.
  - destruct IHmodel_type as [Hta [Hqa Hra]].
    assert (Hvar : forall s, R (d_neut a (d_var s)) (d_neut a' (d_var s))) by
      (intros; apply Hra, ne_related_var).
    split; [| split].
    + intros s. destruct (Hta s) as [A [? ?]].
      destruct (H0 _ _ (Hvar s)) as (b & b' & Hb & Hb').
      destruct (H2 _ _ (Hvar s) _ _ Hb Hb') as [Htb _].
      destruct (Htb (S s)) as [C [? ?]].
      exists (nf_pi A C); split; eapply read_typ_pi; eassumption.
    + intros f f' Hf s. destruct (Hta s) as [A [? ?]].
      destruct (H0 _ _ (Hvar s)) as (b & b' & Hb & Hb').
      destruct (H2 _ _ (Hvar s) _ _ Hb Hb') as [_ [Hqb _]].
      destruct (Hf _ _ (Hvar s)) as (y & y' & Hy & Hy' & Hrel).
      destruct (Hqb _ _ Hrel (S s)) as [M [? ?]].
      exists (nf_fn A M); split; eapply read_nf_fn; eassumption.
    + intros n n' Hn x x' Hx.
      destruct (H0 _ _ Hx) as (b & b' & Hb & Hb').
      destruct (H2 _ _ Hx _ _ Hb Hb') as [_ [_ Hrb]].
      eexists _, _; split; [apply eval_app_neut; exact Hb | split; [apply eval_app_neut; exact Hb' |]].
      apply Hrb. eapply ne_related_app; eassumption.
  - destruct IHmodel_type as [Hta [Hqa Hra]].
    assert (Hvar : forall s, R (d_neut a (d_var s)) (d_neut a' (d_var s))) by
      (intros; apply Hra, ne_related_var).
    split; [| split].
    + intros s. destruct (Hta s) as [A [? ?]].
      destruct (H0 _ _ (Hvar s)) as (b & b' & Hb & Hb').
      destruct (H2 _ _ (Hvar s) _ _ Hb Hb') as [Htb _].
      destruct (Htb (S s)) as [C [? ?]].
      exists (nf_sigma A C); split; eapply read_typ_sigma; eassumption.
    + intros p p' (x & x' & y & y' & Hx & Hx' & Hy & Hy' & HR & HT) s.
      destruct (Hta s) as [A [? ?]].
      destruct (H0 _ _ (Hvar s)) as (b & b' & Hb & Hb').
      destruct (H2 _ _ (Hvar s) _ _ Hb Hb') as [Htb _].
      destruct (Htb (S s)) as [C [? ?]].
      destruct (H0 _ _ HR) as (c & c' & Hc & Hc').
      destruct (H2 _ _ HR _ _ Hc Hc') as [_ [Hqc _]].
      destruct (Hqa _ _ HR s) as [X [? ?]]. destruct (Hqc _ _ HT s) as [Y [? ?]].
      exists (nf_pair X A Y C); split; eapply read_nf_sigma; eassumption.
    + intros n n' Hn.
      assert (Hx : R (d_neut a (d_fst n)) (d_neut a' (d_fst n'))) by
        (apply Hra; now apply ne_related_fst).
      destruct (H0 _ _ Hx) as (b & b' & Hb & Hb').
      destruct (H2 _ _ Hx _ _ Hb Hb') as [_ [_ Hrb]].
      eexists _, _, _, _; repeat split.
      * apply eval_fst_neut.
      * apply eval_fst_neut.
      * apply eval_snd_neut; exact Hb.
      * apply eval_snd_neut; exact Hb'.
      * exact Hx.
      * apply Hrb; now apply ne_related_snd.
  - destruct IHmodel_type as [Hta [Hqa Hra]]; split; [| split].
    + intros s; destruct (Hta s) as [A [? ?]].
      destruct (Hqa _ _ H0 s) as [X [? ?]]; destruct (Hqa _ _ H1 s) as [Y [? ?]].
      exists (nf_eq A X Y); split; eapply read_typ_eq; eassumption.
    + intros v v' Hv s; destruct Hv.
      * destruct (Hta s) as [A [? ?]]; destruct (Hqa _ _ H2 s) as [Z [? ?]].
        exists (nf_refl A Z); split; eapply read_nf_refl; eassumption.
      * destruct (H2 s) as [N [? ?]]; exists (nf_neut N); split; now apply read_nf_eq_neut.
    + intros n n' Hn; now apply eq_rel_neut.
  - destruct IHmodel_type as [Ht [Hm Hr]]; split; [exact Ht | split].
    + intros x y Hxy; apply Hm, H0, Hxy.
    + intros n n' Hnn'; apply H0, Hr, Hnn'.
Qed.

Definition type_rel U : relation := fun a a' => exists R, model_type U a a' R.
Fixpoint universes n : list relation :=
  match n with 0 => nil | S i => let U := universes i in U ++ (type_rel U :: nil) end.

Lemma universes_length : forall n, length (universes n) = n.
Proof. induction n; simpl; [reflexivity | rewrite length_app, IHn; simpl; lia]. Qed.
Lemma universes_lookup : forall j i, i < j -> nth_error (universes j) i = Some (type_rel (universes i)).
Proof.
  induction j as [|j IH]; intros i H; [lia |].
  simpl. rewrite <- (universes_length j) in H.
  destruct (Nat.lt_ge_cases i (length (universes j))) as [Hlt | Hge].
  - rewrite nth_error_app1 by exact Hlt. apply IH. now rewrite universes_length in Hlt.
  - assert (i = length (universes j)) by lia; subst i.
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. now rewrite universes_length.
Qed.
Lemma universes_valid : forall n, universe_model (universes n).
Proof.
  induction n as [|n IH]; intros i R H; [destruct i; discriminate |].
  simpl in H.
  destruct (Nat.lt_ge_cases i (length (universes n))) as [Hlt | Hge].
  - eapply (IH i R). now rewrite nth_error_app1 in H.
  - rewrite nth_error_app2 in H by exact Hge.
    destruct (i - length (universes n)) as [|[|k]]; try discriminate.
    injection H as <-. split.
    + intros a a' [T HT]. exact (proj1 (model_readback _ IH _ _ _ HT)).
    + intros a a' n1 n2 Hn. exists opaque_rel. now apply model_opaque.
Qed.

Lemma model_type_monotone : forall U a a' R, model_type U a a' R ->
    forall V, (forall i T, nth_error U i = Some T -> nth_error V i = Some T) ->
    model_type V a a' R.
Proof.
  intros U a a' R H; induction H; intros V HV; eauto using model_type.
Qed.

Lemma model_type_lift : forall i j a a' R, i <= j ->
    model_type (universes i) a a' R -> model_type (universes j) a a' R.
Proof.
  intros i j a a' R Hij HR; eapply model_type_monotone; [exact HR |].
  intros k T Hk.
  assert (Hki : k < i) by (rewrite <- universes_length; apply nth_error_Some; rewrite Hk; discriminate).
  rewrite universes_lookup in Hk by exact Hki; injection Hk as <-.
  apply universes_lookup; lia.
Qed.

Lemma nbe_from_model : forall Γ M A ρ a m i R,
    initial_env Γ ρ -> eval_exp A ρ a -> eval_exp M ρ m ->
    model_type (universes i) a a R -> R m m ->
    exists W, nbe Γ M A W.
Proof.
  intros Γ M A ρ a m i R Hinit HA HM HT HR.
  destruct (model_readback _ (universes_valid i) _ _ _ HT) as [_ [HQ _]].
  destruct (HQ _ _ HR (length Γ)) as [W [HW _]].
  exists W; eapply nbe_run; eassumption.
Qed.

Definition type_view U a a' R : Prop :=
  match a, a' with
  | d_univ i, d_univ j => i = j /\ exists Q, nth_error U i = Some Q /\ equivalent Q R
  | d_nat, d_nat => equivalent nat_rel R
  | d_neut _ n, d_neut _ n' => ne_related n n' /\ equivalent opaque_rel R
  | d_pi b ρ B, d_pi b' ρ' B' => exists Q T,
      model_type U b b' Q /\ closures Q ρ B ρ' B' /\
      model_codomains U Q ρ B ρ' B' T /\ equivalent (pi_rel Q T) R
  | d_sigma b ρ B, d_sigma b' ρ' B' => exists Q T,
      model_type U b b' Q /\ closures Q ρ B ρ' B' /\
      model_codomains U Q ρ B ρ' B' T /\ equivalent (sigma_rel Q T) R
  | d_eq b x y, d_eq b' x' y' => exists Q,
      model_type U b b' Q /\ Q x x' /\ Q y y' /\ equivalent (eq_rel Q x y x' y') R
  | _, _ => False
  end.

Lemma model_type_view : forall U a b R, model_type U a b R -> type_view U a b R.
Proof.
  intros U a b R H; induction H; cbn.
  - split; [reflexivity | eauto using equiv_refl].
  - apply equiv_refl.
  - split; [assumption | apply equiv_refl].
  - exists R, T. split; [exact H |]. split; [exact H0 |]. split; [exact H1 | apply equiv_refl].
  - exists R, T. split; [exact H |]. split; [exact H0 |]. split; [exact H1 | apply equiv_refl].
  - exists R. split; [exact H |]. split; [exact H0 |]. split; [exact H1 | apply equiv_refl].
  - destruct a, a'; cbn in *; try contradiction;
      repeat match goal with H : ex _ |- _ => destruct H | H : _ /\ _ |- _ => destruct H end;
      eauto 10 using equiv_trans.
Qed.

Lemma pi_rel_equiv : forall R R' T T',
    equivalent R R' -> (forall x x', R x x' -> equivalent (T x x') (T' x x')) ->
    equivalent (pi_rel R T) (pi_rel R' T').
Proof.
  intros R R' T T' HD HC f f'; split; intros H x x' Hx.
  - apply HD in Hx.
    destruct (H _ _ Hx) as (y & y' & Hy & Hy' & HR).
    exists y, y'; repeat split; try assumption. now apply HC in HR.
  - pose proof (proj1 (HD _ _) Hx) as Hx'.
    destruct (H _ _ Hx') as (y & y' & Hy & Hy' & HR).
    exists y, y'; repeat split; try assumption. now apply HC.
Qed.

Lemma sigma_rel_equiv : forall R R' T T',
    equivalent R R' -> (forall x x', R x x' -> equivalent (T x x') (T' x x')) ->
    equivalent (sigma_rel R T) (sigma_rel R' T').
Proof.
  intros R R' T T' HD HC p p'; split; intros (x & x' & y & y' & Hx & Hx' & Hy & Hy' & HR & HT);
    exists x, x', y, y'; repeat split; try assumption.
  - now apply HD.
  - now apply HC.
  - now apply HD.
  - apply HC; [now apply HD | exact HT].
Qed.

Lemma eq_rel_equiv : forall R R' a b c d,
    equivalent R R' -> equivalent (eq_rel R a b c d) (eq_rel R' a b c d).
Proof.
  intros R R' a b c d HE p p'; split; intro H; destruct H;
    first [now apply eq_rel_neut | apply eq_rel_refl; now apply HE].
Qed.

Lemma nat_rel_per : partial_equivalence nat_rel.
Proof.
  split.
  - intros x y H; induction H; constructor; auto using ne_related_sym.
  - intros x y z Hxy; revert z; induction Hxy; intros z Hyz; inversion Hyz; subst;
      constructor; eauto using ne_related_trans.
Qed.

Lemma opaque_rel_per : partial_equivalence opaque_rel.
Proof.
  split.
  - intros x y (a & b & n & m & -> & -> & H).
    exists b, a, m, n; repeat split; now apply ne_related_sym.
  - intros x y z (a & b & n & m & -> & -> & H1) (b' & c & m' & k & HE & -> & H2).
    injection HE as <- <-.
    exists a, c, n, k; repeat split; eauto using ne_related_trans.
Qed.

Definition stable_family (R : relation) (T : domain -> domain -> relation) :=
  (forall x y, R x y -> partial_equivalence (T x y)) /\
  (forall x y y', R x y -> R x y' -> equivalent (T x y) (T x y')) /\
  (forall x x' y, R x y -> R x' y -> equivalent (T x y) (T x' y)).

Lemma stable_family_swap : forall R T, partial_equivalence R -> stable_family R T ->
    forall x y, R x y -> equivalent (T y x) (T x y).
Proof.
  intros R T HP [_ [HL HR]] x y Hxy.
  pose proof (proj1 HP _ _ Hxy) as Hyx.
  pose proof (per_left _ HP _ _ Hxy) as Hxx.
  eapply equiv_trans; [exact (HR _ _ _ Hyx Hxx) | exact (HL _ _ _ Hxx Hxy)].
Qed.

Lemma pi_rel_per : forall R T, partial_equivalence R -> stable_family R T ->
    partial_equivalence (pi_rel R T).
Proof.
  intros R T HD HC; destruct HC as [HP [HL HR]]; split.
  - intros f g H x y Hxy.
    pose proof (proj1 HD _ _ Hxy) as Hyx.
    destruct (H _ _ Hyx) as (u & v & Hu & Hv & Huv).
    exists v, u. split; [exact Hv |]. split; [exact Hu |].
    apply (stable_family_swap _ _ HD (conj HP (conj HL HR)) _ _ Hxy).
    now apply (proj1 (HP _ _ Hyx)).
  - intros f g h Hfg Hgh x y Hxy.
    pose proof (per_right _ HD _ _ Hxy) as Hyy.
    destruct (Hfg _ _ Hxy) as (u & v & Hu & Hv & Huv).
    destruct (Hgh _ _ Hyy) as (v' & w & Hv' & Hw & Hvw).
    resolve_eval.
    exists u, w. split; [exact Hu |]. split; [exact Hw |].
    eapply (proj2 (HP _ _ Hxy)); [exact Huv |].
    now apply (HR _ _ _ Hxy Hyy).
Qed.

Lemma sigma_rel_per : forall R T, partial_equivalence R -> stable_family R T ->
    partial_equivalence (sigma_rel R T).
Proof.
  intros R T HD [HP [HL HR]]; split.
  - intros p p2 (x & y & u & v & Hx & Hy & Hu & Hv & Hxy & Huv).
    exists y, x, v, u; repeat split; try assumption.
    + now apply (proj1 HD).
    + apply (stable_family_swap _ _ HD (conj HP (conj HL HR)) _ _ Hxy).
      now apply (proj1 (HP _ _ Hxy)).
  - intros p p2 p3 (x & y & u & v & Hx & Hy & Hu & Hv & Hxy & Huv)
      (y' & z & v' & w & Hy' & Hz & Hv' & Hw & Hyz & Hvw).
    use_induction_equalities; resolve_eval.
    assert (Hxz : R x z) by (eapply (proj2 HD); eassumption).
    exists x, z, u, w; repeat split; try assumption.
    refine (proj2 (HP _ _ Hxz) u v w _ _).
    + exact (proj1 (HL _ _ _ Hxy Hxz _ _) Huv).
    + exact (proj2 (HR _ _ _ Hxz Hyz _ _) Hvw).
Qed.

Lemma eq_rel_right : forall R x y u v u' v', partial_equivalence R ->
    R u u' -> R v v' -> equivalent (eq_rel R x y u v) (eq_rel R x y u' v').
Proof.
  intros R x y u v u' v' [HS HT] Hu Hv p p';
    split; intro H; destruct H; try (now apply eq_rel_neut); apply eq_rel_refl; eauto.
Qed.
Lemma eq_rel_left : forall R x y x' y' u v, partial_equivalence R ->
    R x x' -> R y y' -> equivalent (eq_rel R x y u v) (eq_rel R x' y' u v).
Proof.
  intros R x y x' y' u v [HS HT] Hx Hy p p';
    split; intro H; destruct H; try (now apply eq_rel_neut); apply eq_rel_refl; eauto.
Qed.
Lemma eq_rel_per : forall R x y x' y', partial_equivalence R -> R x x' -> R y y' ->
    partial_equivalence (eq_rel R x y x' y').
Proof.
  intros R x y x' y' [HS HT] Hx Hy; split.
  - intros p p2 H; destruct H;
      [apply eq_rel_refl; eauto 6 | apply eq_rel_neut; now apply ne_related_sym].
  - intros p p2 p3 H H'; destruct H; inversion H'; subst;
      [apply eq_rel_refl; eauto 6 | apply eq_rel_neut; eauto using ne_related_trans].
Qed.

Definition type_properties U a b R :=
  partial_equivalence R /\
  (forall c T, model_type U a c T -> equivalent R T) /\
  (forall c T, model_type U c b T -> equivalent R T).

Lemma stable_model_family : forall U R ρ B ρ' B' T,
    closures R ρ B ρ' B' ->
    (forall x y, R x y -> forall b b',
      eval_exp B (extend_env ρ x) b ->
      eval_exp B' (extend_env ρ' y) b' -> type_properties U b b' (T x y)) ->
    model_codomains U R ρ B ρ' B' T ->
    stable_family R T.
Proof.
  intros U R ρ B ρ' B' T HE HP HC; split; [| split].
  - intros x y Hxy. destruct (HE _ _ Hxy) as (b & b' & Hb & Hb').
    exact (proj1 (HP _ _ Hxy _ _ Hb Hb')).
  - intros x y z Hxy Hxz.
    destruct (HE _ _ Hxy) as (b & b' & Hb & Hb').
    destruct (HE _ _ Hxz) as (c & c' & Hc & Hc').
    resolve_eval.
    eapply (proj1 (proj2 (HP _ _ Hxy _ _ Hb Hb'))).
    exact (HC _ _ Hxz _ _ Hb Hc').
  - intros x z y Hxy Hzy.
    destruct (HE _ _ Hxy) as (b & b' & Hb & Hb').
    destruct (HE _ _ Hzy) as (c & c' & Hc & Hc').
    resolve_eval.
    eapply (proj2 (proj2 (HP _ _ Hxy _ _ Hb Hb'))).
    exact (HC _ _ Hzy _ _ Hc Hb').
Qed.

Ltac codomain_coherence Hcl Hcod HS HQ HC :=
  intros x y Hxy;
  let Hqy := fresh "Hqy" in
  assert (Hqy : _) by exact (proj1 (HQ x y) Hxy);
  let b := fresh "b" in let b' := fresh "b'" in
  let c := fresh "c" in let c' := fresh "c'" in
  let Hb := fresh "Hb" in let Hb' := fresh "Hb'" in
  let Hc := fresh "Hc" in let Hc' := fresh "Hc'" in
  destruct (Hcl _ _ Hxy) as (b & b' & Hb & Hb');
  destruct (HS _ _ Hqy) as (c & c' & Hc & Hc');
  resolve_eval;
  let Hlc := fresh "Hlc" in let Hrc := fresh "Hrc" in
  destruct (Hcod _ _ Hxy _ _ Hb Hb') as [_ [Hlc Hrc]];
  first [eapply Hlc; solve [eapply HC; eassumption] | eapply Hrc; solve [eapply HC; eassumption]].

Definition universe_pers U :=
  forall i R, nth_error U i = Some R -> partial_equivalence R.

Lemma model_type_properties : forall U, universe_pers U ->
    forall a b R, model_type U a b R -> type_properties U a b R.
Proof.
  intros U HU a b R H; induction H.
  - split; [eauto | split]; intros c Q HQ;
      apply model_type_view in HQ; destruct c; cbn in HQ; try contradiction;
      destruct HQ as [E [V [HV HE]]]; subst; rewrite H in HV; now injection HV as <-.
  - split; [apply nat_rel_per | split];
      intros c Q HQ; apply model_type_view in HQ; destruct c; cbn in HQ; tauto.
  - split; [apply opaque_rel_per | split];
      intros c Q HQ; apply model_type_view in HQ; destruct c; cbn in HQ; tauto.
  - destruct IHmodel_type as [HP [HL HR]].
    split.
    + apply pi_rel_per; [exact HP |]. eapply stable_model_family; eassumption.
    + split; intros c V HV; apply model_type_view in HV; destruct c; cbn in HV; try contradiction;
        destruct HV as (Q & T' & HQ & HS & HC & HE);
        (eapply equiv_trans; [|exact HE]); apply pi_rel_equiv.
      * now apply HL in HQ.
      * pose proof (HL _ _ HQ) as HD. codomain_coherence H0 H2 HS HD HC.
      * now apply HR in HQ.
      * pose proof (HR _ _ HQ) as HD. codomain_coherence H0 H2 HS HD HC.
  - destruct IHmodel_type as [HP [HL HR]].
    split.
    + apply sigma_rel_per; [exact HP |]. eapply stable_model_family; eassumption.
    + split; intros c V HV; apply model_type_view in HV; destruct c; cbn in HV; try contradiction;
        destruct HV as (Q & T' & HQ & HS & HC & HE);
        (eapply equiv_trans; [|exact HE]); apply sigma_rel_equiv.
      * now apply HL in HQ.
      * pose proof (HL _ _ HQ) as HD. codomain_coherence H0 H2 HS HD HC.
      * now apply HR in HQ.
      * pose proof (HR _ _ HQ) as HD. codomain_coherence H0 H2 HS HD HC.
  - destruct IHmodel_type as [HP [HL HR]].
    split; [eauto using eq_rel_per | split].
    + intros c V HV. apply model_type_view in HV. destruct c; cbn in HV; try contradiction.
      destruct HV as (Q & HQ & HX & HY & HE).
      pose proof (HL _ _ HQ) as HD.
      pose proof (per_equiv _ _ HD HP) as HPQ.
      eapply equiv_trans; [|exact HE].
      eapply equiv_trans; [now apply eq_rel_equiv |].
      apply eq_rel_right; [exact HPQ | |];
        (eapply (proj2 HPQ); [apply (proj1 HPQ); apply HD; eassumption | eassumption]).
    + intros c V HV. apply model_type_view in HV. destruct c; cbn in HV; try contradiction.
      destruct HV as (Q & HQ & HX & HY & HE).
      pose proof (HR _ _ HQ) as HD.
      pose proof (per_equiv _ _ HD HP) as HPQ.
      eapply equiv_trans; [|exact HE].
      eapply equiv_trans; [now apply eq_rel_equiv |].
      apply eq_rel_left; [exact HPQ | |];
        (eapply (proj2 HPQ); [apply HD; eassumption | apply (proj1 HPQ); eassumption]).
  - destruct IHmodel_type as [HP [HL HR]].
    split; [now eapply per_equiv | split]; intros c Q HQ;
      (eapply equiv_trans; [now apply equiv_sym | eauto]).
Qed.

Lemma closures_flip : forall R ρ B ρ' B', partial_equivalence R ->
    closures R ρ B ρ' B' -> closures R ρ' B' ρ B.
Proof.
  intros R ρ B ρ' B' [HS _] H x y Hxy.
  destruct (H y x (HS _ _ Hxy)) as (b & b' & Hb & Hb'); eauto.
Qed.

Lemma model_type_flip : forall U, universe_pers U ->
    forall a b R, model_type U a b R -> model_type U b a R.
Proof.
  intros U HU a b R H; induction H.
  - now apply model_univ.
  - apply model_nat.
  - apply model_opaque; now apply ne_related_sym.
  - pose proof (proj1 (model_type_properties _ HU _ _ _ H)) as HP.
    assert (HC : stable_family R T).
    { eapply stable_model_family; [exact H0 | | exact H1]. intros; eapply model_type_properties; eauto. }
    apply model_pi; [exact IHmodel_type | now apply closures_flip |].
    intros x y Hxy b b' Hb Hb'. eapply model_ext.
    + eapply H2; [exact (proj1 HP _ _ Hxy) | exact Hb' | exact Hb].
    + exact (stable_family_swap _ _ HP HC _ _ Hxy).
  - pose proof (proj1 (model_type_properties _ HU _ _ _ H)) as HP.
    assert (HC : stable_family R T).
    { eapply stable_model_family; [exact H0 | | exact H1]. intros; eapply model_type_properties; eauto. }
    apply model_sigma; [exact IHmodel_type | now apply closures_flip |].
    intros x y Hxy b b' Hb Hb'. eapply model_ext.
    + eapply H2; [exact (proj1 HP _ _ Hxy) | exact Hb' | exact Hb].
    + exact (stable_family_swap _ _ HP HC _ _ Hxy).
  - pose proof (proj1 (model_type_properties _ HU _ _ _ H)) as [HS HT].
    eapply model_ext.
    + eapply model_eq; [exact IHmodel_type | now apply HS | now apply HS].
    + eapply equiv_trans.
      * apply eq_rel_left; [now split | exact (HS _ _ H0) | exact (HS _ _ H1)].
      * apply eq_rel_right; [now split | exact H0 | exact H1].
  - eapply model_ext; eassumption.
Qed.

Lemma closures_compose : forall R Q ρ B ρ' B' ρ'' B'', partial_equivalence R ->
    equivalent R Q -> closures R ρ B ρ' B' -> closures Q ρ' B' ρ'' B'' ->
    closures R ρ B ρ'' B''.
Proof.
  intros R Q ρ B ρ' B' ρ'' B'' HP HE H1 H2 x z Hz.
  destruct (H1 x z Hz) as (b & b' & Hb & Hb').
  assert (Hzz : Q z z) by (apply HE; exact (per_right _ HP _ _ Hz)).
  destruct (H2 z z Hzz) as (c & c' & Hc & Hc'); eauto.
Qed.

Lemma model_codomains_compose : forall U R Q ρ B ρ' B' ρ'' B'' T T',
    partial_equivalence R -> equivalent R Q ->
    closures R ρ B ρ' B' -> closures Q ρ' B' ρ'' B'' ->
    model_codomains U Q ρ' B' ρ'' B'' T' ->
    (forall x y, R x y -> forall b b',
      eval_exp B (extend_env ρ x) b -> eval_exp B' (extend_env ρ' y) b' ->
      forall c V, model_type U b' c V -> model_type U b c (T x y)) ->
    model_codomains U R ρ B ρ'' B'' T.
Proof.
  intros U R Q ρ B ρ' B' ρ'' B'' T T' HP HE HE1 HE2 HC HI x z Hxz b c Hb Hc.
  destruct (HE1 x z Hxz) as (a & b' & Ha & Hb').
  assert (Hzz : Q z z) by (apply HE; exact (per_right _ HP _ _ Hxz)).
  destruct (HE2 z z Hzz) as (a' & c' & Ha' & Hc').
  resolve_eval. eapply HI; [exact Hxz | exact Hb | exact Hb' |].
  eapply HC; eassumption.
Qed.

Lemma model_type_compose : forall U, universe_pers U ->
    forall a b R, model_type U a b R ->
    forall c T, model_type U b c T -> model_type U a c R.
Proof.
  intros U HU a b R H; induction H; intros c V HV.
  1-6: apply model_type_view in HV; destruct c; cbn in HV; try contradiction.
  - destruct HV as [<- _]. now apply model_univ.
  - apply model_nat.
  - destruct HV as [Hn _]. apply model_opaque. eapply ne_related_trans; eassumption.
  - destruct HV as (Q & T' & HV & HE & HC & _).
    destruct (model_type_properties _ HU _ _ _ H) as [HP [_ HR]].
    pose proof (model_type_properties _ HU _ _ _ HV) as [_ [HL _]].
    assert (HQ : equivalent R Q) by
      (eapply equiv_sym, HL; exact (model_type_flip _ HU _ _ _ H)).
    apply model_pi; [exact (IHmodel_type _ _ HV) | |].
    + eapply closures_compose; eassumption.
    + eapply model_codomains_compose; eassumption.
  - destruct HV as (Q & T' & HV & HE & HC & _).
    destruct (model_type_properties _ HU _ _ _ H) as [HP [_ HR]].
    pose proof (model_type_properties _ HU _ _ _ HV) as [_ [HL _]].
    assert (HQ : equivalent R Q) by
      (eapply equiv_sym, HL; exact (model_type_flip _ HU _ _ _ H)).
    apply model_sigma; [exact (IHmodel_type _ _ HV) | |].
    + eapply closures_compose; eassumption.
    + eapply model_codomains_compose; eassumption.
  - destruct HV as (Q & HV & Hx & Hy & _).
    destruct (model_type_properties _ HU _ _ _ H) as [[HS HB] [_ HR]].
    pose proof (model_type_properties _ HU _ _ _ HV) as [_ [HL _]].
    assert (HQ : equivalent R Q) by
      (eapply equiv_sym, HL; exact (model_type_flip _ HU _ _ _ H)).
    eapply model_ext.
    + apply model_eq with (R := R).
      * exact (IHmodel_type _ _ HV).
      * eapply HB; [exact H0 | exact (proj2 (HQ _ _) Hx)].
      * eapply HB; [exact H1 | exact (proj2 (HQ _ _) Hy)].
    + apply eq_rel_right; [now split | |]; apply HS; now apply HQ.
  - eapply model_ext; [exact (IHmodel_type _ _ HV) | exact H0].
Qed.

Lemma universes_per : forall n, universe_pers (universes n).
Proof.
  induction n as [|n IH]; intros i R H; [destruct i; discriminate |].
  simpl in H.
  destruct (Nat.lt_ge_cases i (length (universes n))) as [Hlt | Hge].
  - apply (IH i). now rewrite nth_error_app1 in H.
  - rewrite nth_error_app2 in H by exact Hge.
    destruct (i - length (universes n)) as [|[|k]]; try discriminate.
    injection H as <-; split.
    + intros a a' [T HT]; exists T; exact (model_type_flip _ IH _ _ _ HT).
    + intros a b c [T HT] [V HV]; exists T; eapply model_type_compose; eauto.
Qed.

Definition at_type i := model_type (universes i).
Lemma at_type_per : forall i a b R, at_type i a b R -> partial_equivalence R.
Proof. intros; eapply (proj1 (model_type_properties _ (universes_per i) _ _ _ H)). Qed.
Lemma at_type_sym : forall i a b R, at_type i a b R -> at_type i b a R.
Proof. intros; eapply model_type_flip; eauto using universes_per. Qed.
Lemma at_type_trans : forall i j a b c R T, at_type i a b R -> at_type j b c T ->
    at_type (Nat.max i j) a c R.
Proof.
  intros i j a b c R T H HT. eapply model_type_compose; [apply universes_per | |].
  - eapply model_type_lift; [apply Nat.le_max_l | exact H].
  - eapply model_type_lift; [apply Nat.le_max_r | exact HT].
Qed.
Lemma at_type_coherent_l : forall i j a b c R T,
    at_type i a b R -> at_type j a c T -> equivalent R T.
Proof.
  intros i j a b c R T H HT.
  pose proof (model_type_lift _ _ _ _ _ (Nat.le_max_l i j) H) as HL.
  pose proof (model_type_lift _ _ _ _ _ (Nat.le_max_r i j) HT) as HR.
  exact (proj1 (proj2 (model_type_properties _ (universes_per _) _ _ _ HL)) _ _ HR).
Qed.
Lemma at_type_coherent_r : forall i j a b c R T,
    at_type i a c R -> at_type j b c T -> equivalent R T.
Proof. eauto using at_type_coherent_l, at_type_sym. Qed.
Lemma at_type_self_l : forall i a b R, at_type i a b R -> at_type i a a R.
Proof.
  intros i a b R H; eapply model_type_compose; [apply universes_per | exact H | exact (at_type_sym _ _ _ _ H)].
Qed.
Lemma at_type_self_r : forall i a b R, at_type i a b R -> at_type i b b R.
Proof. eauto using at_type_self_l, at_type_sym. Qed.

Lemma choose_family : forall i R ρ B ρ' B',
    (forall x x', R x x' -> exists b b' T,
       eval_exp B (extend_env ρ x) b /\ eval_exp B' (extend_env ρ' x') b' /\ at_type i b b' T) ->
    exists T, closures R ρ B ρ' B' /\ model_codomains (universes i) R ρ B ρ' B' T.
Proof.
  intros i R ρ B ρ' B' H.
  exists (fun x x' y y' => exists b b' Q,
     eval_exp B (extend_env ρ x) b /\ eval_exp B' (extend_env ρ' x') b' /\ at_type i b b' Q /\ Q y y').
  split.
  - intros x x' Hx. destruct (H _ _ Hx) as (b & b' & Q & Hb & Hb' & HQ); eauto.
  - intros x x' Hx b b' Hb Hb'.
    destruct (H _ _ Hx) as (c & c' & T & Hc & Hc' & HT); resolve_eval.
    eapply model_ext; [exact HT |].
    intros y y'; split; [eauto 8 |].
    intros (f & f' & Q & Hf & Hf' & HQ & Hy); resolve_eval.
    exact (proj2 (at_type_coherent_l _ _ _ _ _ _ _ HT HQ _ _) Hy).
Qed.

Definition type_values a a' R := exists i, at_type i a a' R.

Lemma type_values_per : forall a a' R, type_values a a' R -> partial_equivalence R.
Proof. intros a a' R [i H]; eauto using at_type_per. Qed.
Lemma type_values_left : forall a b R, type_values a b R -> type_values a a R.
Proof. intros a b R [i H]; exists i; eauto using at_type_self_l. Qed.
Lemma type_values_right : forall a b R, type_values a b R -> type_values b b R.
Proof. intros a b R [i H]; exists i; eauto using at_type_self_r. Qed.
Lemma type_values_sym : forall a b R, type_values a b R -> type_values b a R.
Proof. intros a b R [i H]; exists i; eauto using at_type_sym. Qed.
Lemma type_values_trans : forall a b c R T,
    type_values a b R -> type_values b c T -> type_values a c R.
Proof. intros a b c R T [i Hi] [j Hj]; eexists; eauto using at_type_trans. Qed.
Lemma type_values_equiv_l : forall a b c R T,
    type_values a b R -> type_values a c T -> equivalent R T.
Proof. intros a b c R T [i Hi] [j Hj]; eauto using at_type_coherent_l. Qed.
Lemma type_values_equiv_r : forall a b c R T,
    type_values a c R -> type_values b c T -> equivalent R T.
Proof. intros a b c R T [i Hi] [j Hj]; eauto using at_type_coherent_r. Qed.

Fixpoint env_related (Γ : ctx) (ρ ρ' : env) : Prop :=
  match Γ with
  | nil => True
  | A :: Δ =>
      env_related Δ (drop_env ρ) (drop_env ρ') /\
      exists a a' R, eval_exp A (drop_env ρ) a /\ eval_exp A (drop_env ρ') a' /\
                     type_values a a' R /\ R (ρ 0) (ρ' 0) /\
                     ρ = extend_env (drop_env ρ) (ρ 0) /\
                     ρ' = extend_env (drop_env ρ') (ρ' 0)
  end.

Lemma env_related_extend : forall Γ A ρ ρ' a a' R x x',
    env_related Γ ρ ρ' -> eval_exp A ρ a -> eval_exp A ρ' a' ->
    type_values a a' R -> R x x' ->
    env_related (A :: Γ) (extend_env ρ x) (extend_env ρ' x').
Proof. intros; simpl; eauto 10. Qed.

Lemma env_related_per : forall Γ, forall ρ ρ',
    env_related Γ ρ ρ' ->
    env_related Γ ρ' ρ /\ env_related Γ ρ ρ /\ env_related Γ ρ' ρ'.
Proof.
  induction Γ as [|A Γ IH]; [intros; repeat split |].
  intros ρ ρ' [HE (a & a' & R & Ha & Ha' & HT & HR & Heta & Heta')].
  destruct (IH _ _ HE) as [Hs [Hl Hr]].
  destruct (type_values_per _ _ _ HT) as [HS HC].
  split; [|split]; cbn [env_related]; split; try assumption.
  - exists a', a, R. repeat split; eauto using type_values_sym.
  - exists a, a, R. repeat split; eauto using type_values_left.
  - exists a', a', R. repeat split; eauto using type_values_right.
Qed.

Definition eval_pair (ρ ρ' : env) (M N : exp) (R : relation) :=
  exists m n, eval_exp M ρ m /\ eval_exp N ρ' n /\ R m n.

Definition type_pair ρ ρ' A B R :=
  eval_pair ρ ρ' A B (fun a b => type_values a b R).

Definition exp_related_at ρ ρ' A M N :=
  exists R, type_pair ρ ρ' A A R /\ eval_pair ρ ρ' M N R.

Definition exp_related Γ A M N :=
  forall ρ ρ', env_related Γ ρ ρ' -> exp_related_at ρ ρ' A M N.

Definition sub_related Γ Δ σ τ :=
  forall ρ ρ', env_related Γ ρ ρ' ->
    exists θ θ', eval_sub σ ρ θ /\ eval_sub τ ρ' θ' /\ env_related Δ θ θ'.

Definition context_related Γ Δ :=
  forall ρ ρ', env_related Γ ρ ρ' -> env_related Δ ρ ρ'.

Definition subtype_related Γ A B :=
  forall ρ ρ', env_related Γ ρ ρ' ->
    exists R T, type_pair ρ ρ' A A R /\ type_pair ρ ρ' B B T /\ includes R T.

Definition env_has_initial Γ :=
  exists ρ, initial_env Γ ρ /\ env_related Γ ρ ρ.

Lemma typed_universe_value : forall i, at_type (S i) (d_univ i) (d_univ i) (type_rel (universes i)).
Proof. intros i; apply model_univ, universes_lookup; lia. Qed.
Lemma at_universe : forall ρ ρ' M N i,
    eval_pair ρ ρ' M N (type_rel (universes i)) -> exp_related_at ρ ρ' (a_typ i) M N.
Proof.
  intros ρ ρ' M N i H. exists (type_rel (universes i)); split; [|exact H].
  exists (d_univ i), (d_univ i). repeat split; try apply eval_exp_typ.
  exists (S i); apply typed_universe_value.
Qed.
Lemma from_universe : forall ρ ρ' M N i,
    exp_related_at ρ ρ' (a_typ i) M N -> eval_pair ρ ρ' M N (type_rel (universes i)).
Proof.
  intros ρ ρ' M N i (R & (a & a' & HA & HA' & [j HT]) & HM).
  inversion HA; inversion HA'; subst; clear HA HA'.
  apply model_type_view in HT; cbn in HT. destruct HT as [_ [T [Hlookup HE]]].
  assert (Hlt : i < j) by (rewrite <- universes_length; apply nth_error_Some; rewrite Hlookup; discriminate).
  rewrite universes_lookup in Hlookup by exact Hlt; injection Hlookup as <-.
  destruct HM as (m & n & Hm & Hn & HR).
  exists m, n; repeat split; try assumption; now apply HE.
Qed.
Lemma at_nat : forall ρ ρ' M N,
    eval_pair ρ ρ' M N nat_rel -> exp_related_at ρ ρ' a_nat M N.
Proof.
  intros ρ ρ' M N H. exists nat_rel; split; [|exact H].
  exists d_nat, d_nat. repeat split; try apply eval_exp_nat.
  exists 0; apply model_nat.
Qed.
Lemma from_nat : forall ρ ρ' M N,
    exp_related_at ρ ρ' a_nat M N -> eval_pair ρ ρ' M N nat_rel.
Proof.
  intros ρ ρ' M N (R & (a & a' & HA & HA' & [j HT]) & HM).
  inversion HA; inversion HA'; subst; clear HA HA'.
  apply model_type_view in HT; cbn in HT.
  destruct HM as (m & n & Hm & Hn & HR).
  exists m, n; repeat split; try assumption; now apply HT.
Qed.
Lemma exp_related_sym : forall Γ A M N, exp_related Γ A M N -> exp_related Γ A N M.
Proof.
  intros Γ A M N H ρ ρ' HE.
  destruct (H ρ' ρ (proj1 (env_related_per _ _ _ HE)))
    as (R & (a' & a & HA' & HA & HT) & m & n & HM & HN & HR).
  exists R. split.
  - exists a, a'; repeat split; eauto using type_values_sym.
  - exists n, m; repeat split; try assumption.
    exact (proj1 (type_values_per _ _ _ HT) _ _ HR).
Qed.
Lemma exp_related_trans : forall Γ A M N P,
    exp_related Γ A M N -> exp_related Γ A N P -> exp_related Γ A M P.
Proof.
  intros Γ A M N P H1 H2 ρ ρ' HE.
  destruct (H1 _ _ HE) as (R & (a & a' & HA & HA' & HT) & m & n & HM & HN & HR).
  destruct (H2 ρ' ρ' (proj2 (proj2 (env_related_per _ _ _ HE))))
    as (T & (b & b' & HB & HB' & HV) & n' & p & HN' & HP & HQ).
  resolve_eval.
  pose proof (type_values_equiv_r _ _ _ _ _ HT HV) as HX.
  exists R; split; [exists a, a'; tauto |].
  exists m, p; repeat split; try assumption.
  exact (proj2 (type_values_per _ _ _ HT) _ _ _ HR (proj2 (HX _ _) HQ)).
Qed.
Lemma exp_related_subtype : forall Γ A B M N,
    exp_related Γ A M N -> subtype_related Γ A B -> exp_related Γ B M N.
Proof.
  intros Γ A B M N H HS ρ ρ' HE.
  destruct (H _ _ HE) as (R & (a & a' & HA & HA' & HT) & m & n & HM & HN & HR).
  destruct (HS _ _ HE) as (R' & T & (b & b' & HB & HB' & HT') & HTT & HI).
  resolve_eval.
  pose proof (type_values_equiv_l _ _ _ _ _ HT HT') as HX.
  exists T; split; [exact HTT |].
  exists m, n; repeat split; try assumption.
  apply HI, HX, HR.
Qed.


Lemma env_related_trans : forall Γ ρ1 ρ2 ρ3,
    env_related Γ ρ1 ρ2 -> env_related Γ ρ2 ρ3 -> env_related Γ ρ1 ρ3.
Proof.
  induction Γ as [| A Γ IH]; [intros; exact I |].
  intros ρ1 ρ2 ρ3
    [HE (a & b & R & Ha & Hb & HT & HR & Heta1 & Heta2)]
    [HE' (b' & c & T & Hb' & Hc & HT' & HR' & Heta2' & Heta3)].
  resolve_eval.
  cbn [env_related]; split; [eauto |].
  exists a, c, R; split; [exact Ha |]; split; [exact Hc |]; split.
  - eauto using type_values_trans.
  - pose proof (type_values_equiv_r _ _ _ _ _ HT (type_values_sym _ _ _ HT')) as HQ.
    split; [exact (proj2 (type_values_per _ _ _ HT) _ _ _ HR (proj2 (HQ _ _) HR')) | tauto].
Qed.

Lemma sub_related_sym : forall Γ Δ σ τ,
    sub_related Γ Δ σ τ -> sub_related Γ Δ τ σ.
Proof.
  intros Γ Δ σ τ H ρ ρ' HE.
  destruct (H _ _ (proj1 (env_related_per _ _ _ HE))) as (θ & θ' & Hθ & Hθ' & HD).
  exists θ', θ; repeat split; try assumption.
  exact (proj1 (env_related_per _ _ _ HD)).
Qed.

Lemma sub_related_trans : forall Γ Δ σ τ υ,
    sub_related Γ Δ σ τ -> sub_related Γ Δ τ υ -> sub_related Γ Δ σ υ.
Proof.
  intros Γ Δ σ τ υ H1 H2 ρ ρ' HE.
  destruct (H1 _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  destruct (H2 _ _ (proj2 (proj2 (env_related_per _ _ _ HE)))) as (χ & χ' & Hχ & Hχ' & HD').
  resolve_eval.
  exists θ, χ'; split; [assumption | split; [assumption | eauto using env_related_trans]].
Qed.

Lemma sub_related_self_l : forall Γ Δ σ τ,
    sub_related Γ Δ σ τ -> sub_related Γ Δ σ σ.
Proof. eauto using sub_related_trans, sub_related_sym. Qed.

Lemma exp_related_substitution : forall Γ Δ A M N σ τ,
    sub_related Γ Δ σ τ -> exp_related Δ A M N ->
    exp_related Γ (a_sub A σ) (a_sub M σ) (a_sub N τ).
Proof.
  intros Γ Δ A M N σ τ Hσ HM ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  destruct (sub_related_self_l _ _ _ _ Hσ _ _ HE) as (χ & χ' & Hχ & Hχ' & HD').
  resolve_eval.
  destruct (HM _ _ HD) as (R & (a & a' & Ha & Ha' & HT) & m & n & Hm & Hn & HR).
  destruct (HM _ _ HD') as (T & (b & b' & Hb & Hb' & HT') & _).
  resolve_eval.
  pose proof (type_values_equiv_l _ _ _ _ _ HT HT') as HX.
  exists T; split.
  - exists a, b'; split; [eapply eval_exp_sub; eassumption |].
    split; [eapply eval_exp_sub; eassumption | exact HT'].
  - exists m, n; split; [eapply eval_exp_sub; eassumption |].
    split; [eapply eval_exp_sub; eassumption | now apply HX].
Qed.


Lemma type_pair_coherent_l : forall ρ ρ' ρ'' A B C R T,
    type_pair ρ ρ' A B R -> type_pair ρ ρ'' A C T -> equivalent R T.
Proof.
  intros ???????? (a & b & Ha & Hb & H) (a' & c & Ha' & Hc & H').
  resolve_eval. eauto using type_values_equiv_l.
Qed.



Lemma semantic_initial_cons : forall Γ A i,
    env_has_initial Γ -> exp_related Γ (a_typ i) A A -> env_has_initial (A :: Γ).
Proof.
  intros Γ A i (ρ & Hinit & HE) H.
  destruct (from_universe _ _ _ _ _ (H _ _ HE)) as (a & a' & Ha & Ha' & R & HT); resolve_eval.
  exists (extend_env ρ (d_neut a (d_var (length Γ)))); split.
  - now constructor.
  - eapply env_related_extend; [exact HE | exact Ha | exact Ha | exists i; exact HT |].
    destruct (model_readback _ (universes_valid i) _ _ _ HT) as [_ [_ HR]].
    apply HR, ne_related_var.
Qed.

Lemma semantic_var : forall Γ A x,
    ctx_lookup x A Γ -> exp_related Γ A (a_var x) (a_var x).
Proof.
  intros Γ A x H; induction H.
  - intros ρ ρ' [HE (a & a' & R & Ha & Ha' & HT & HR & _ & _)].
    exists R; split.
    + exists a, a'; repeat split; try assumption; (eapply eval_exp_sub; [apply eval_sub_weaken | eassumption]).
    + exists (ρ 0), (ρ' 0); repeat split; try assumption; apply eval_exp_var.
  - intros ρ ρ' [HE _].
    destruct (IHctx_lookup _ _ HE) as (R & (a & a' & Ha & Ha' & HT) & m & m' & Hm & Hm' & HR).
    inversion Hm; inversion Hm'; subst.
    exists R; split.
    + exists a, a'; repeat split; try assumption; (eapply eval_exp_sub; [apply eval_sub_weaken | eassumption]).
    + exists (ρ (S n)), (ρ' (S n)); repeat split; try assumption; apply eval_exp_var.
Qed.

Lemma semantic_subtype_convert : forall Γ A B i,
    exp_related Γ (a_typ i) A B -> subtype_related Γ A B.
Proof.
  intros Γ A B i H ρ ρ' HE.
  destruct (from_universe _ _ _ _ _ (H _ _ HE)) as (a & b & Ha & Hb & R & HT).
  destruct (from_universe _ _ _ _ _ (H _ _ (proj2 (proj2 (env_related_per _ _ _ HE))))) as
    (a' & b' & Ha' & Hb' & T & HS).
  destruct (from_universe _ _ _ _ _ (H _ _ (proj1 (proj2 (env_related_per _ _ _ HE))))) as
    (ax & bx & Hax & Hbx & V & HV).
  resolve_eval.
  pose proof (at_type_trans _ _ _ _ _ _ _ HT (at_type_sym _ _ _ _ HS)) as HAA'.
  pose proof (at_type_trans _ _ _ _ _ _ _ (at_type_sym _ _ _ _ HV) HT) as HBB'.
  pose proof (at_type_coherent_l _ _ _ _ _ _ _ HV HT) as HX.
  exists R, V; split; [| split].
  - exists a, a'; split; [exact Ha |]. split; [exact Ha' |]. eexists; exact HAA'.
  - exists bx, b; split; [exact Hbx |]. split; [exact Hb |]. eexists; exact HBB'.
  - intros m n HR; now apply HX.
Qed.

Lemma semantic_subtype_trans : forall Γ A B C,
    subtype_related Γ A B -> subtype_related Γ B C -> subtype_related Γ A C.
Proof.
  intros Γ A B C H1 H2 ρ ρ' HE.
  destruct (H1 _ _ HE) as (R & T & HRA & HTB & HI).
  destruct (H2 _ _ HE) as (V & U & HVB & HUC & HJ).
  pose proof (type_pair_coherent_l _ _ _ _ _ _ _ _ HTB HVB) as HX.
  exists R, U; repeat split; try assumption.
  intros x y HR; apply HJ, HX, HI, HR.
Qed.

Lemma semantic_subtype_univ : forall Γ i j, i < j -> subtype_related Γ (a_typ i) (a_typ j).
Proof.
  intros Γ i j Hρ ρ ρ' _.
  exists (type_rel (universes i)), (type_rel (universes j)); split; [|split].
  - exists (d_univ i), (d_univ i); repeat split; try apply eval_exp_typ.
    exists (S i); apply typed_universe_value.
  - exists (d_univ j), (d_univ j); repeat split; try apply eval_exp_typ.
    exists (S j); apply typed_universe_value.
  - intros a b [R HR]. exists R. eapply (model_type_lift i j); [lia | exact HR].
Qed.

Lemma semantic_context_extend : forall Γ Δ A B,
    context_related Γ Δ -> subtype_related Γ A B ->
    context_related (A :: Γ) (B :: Δ).
Proof.
  intros Γ Δ A B Hctx Hsub ρ ρ' [HE (a & a' & R & Ha & Ha' & HR & Hx & Heta & Heta')].
  cbn [env_related]; split; [now apply Hctx |].
  destruct (Hsub _ _ HE) as (T & V & (b & b' & Hb & Hb' & HT) & HV & HI).
  resolve_eval. destruct HV as (c & c' & Hc & Hc' & HV).
  pose proof (type_values_equiv_l _ _ _ _ _ HR HT) as HX.
  exists c, c', V; split; [exact Hc |]; split; [exact Hc' |]; split; [exact HV |].
  split; [now apply HI, HX | tauto].
Qed.

Definition kind_at i Γ A :=
  forall ρ ρ', env_related Γ ρ ρ' ->
    eval_pair ρ ρ' A A (type_rel (universes i)).
Definition kind_bounded Γ A := exists i, kind_at i Γ A.
Definition term_valid Γ A M N := exp_related Γ A M N /\ kind_bounded Γ A.

Lemma kind_from_typing : forall i Γ A, exp_related Γ (a_typ i) A A -> kind_at i Γ A.
Proof. intros i Γ A H ρ ρ' HE; now apply from_universe, H. Qed.

Lemma kind_lift : forall i j Γ A, i <= j -> kind_at i Γ A -> kind_at j Γ A.
Proof.
  intros i j Γ A Hij H ρ ρ' HE.
  destruct (H _ _ HE) as (a & a' & Ha & Ha' & R & HT).
  exists a, a'; repeat split; try assumption.
  exists R; eauto using model_type_lift.
Qed.

Lemma kind_universe : forall i Γ, kind_at (S i) Γ (a_typ i).
Proof.
  intros i Γ ρ ρ' _; exists (d_univ i), (d_univ i); repeat split; try constructor.
  eexists; apply typed_universe_value.
Qed.

Lemma kind_nat : forall Γ, kind_at 0 Γ a_nat.
Proof.
  intros Γ ρ ρ' _; exists d_nat, d_nat; repeat split; try constructor.
  exists nat_rel; apply model_nat.
Qed.

Lemma kind_subst : forall i Γ Δ A σ,
    sub_related Γ Δ σ σ -> kind_at i Δ A -> kind_at i Γ (a_sub A σ).
Proof.
  intros i Γ Δ A σ Hσ HA ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  destruct (HA _ _ HD) as (a & a' & Ha & Ha' & R & HT).
  exists a, a'; repeat split; try (eapply eval_exp_sub; eassumption).
  now exists R.
Qed.
Lemma kind_bounded_subst : forall Γ Δ A σ,
    sub_related Γ Δ σ σ -> kind_bounded Δ A -> kind_bounded Γ (a_sub A σ).
Proof. intros Γ Δ A σ HS [i Hi]; exists i; eauto using kind_subst. Qed.

Lemma prepare_binder : forall i j Γ A A' B B' ρ ρ',
    env_related Γ ρ ρ' ->
    kind_at i Γ A ->
    eval_pair ρ ρ' A A' (type_rel (universes i)) ->
    (forall θ θ', env_related (A :: Γ) θ θ' -> eval_pair θ θ' B B' (type_rel (universes j))) ->
    exists a a' R T,
      eval_exp A ρ a /\ eval_exp A' ρ' a' /\ at_type i a a' R /\
      closures R ρ B ρ' B' /\ model_codomains (universes j) R ρ B ρ' B' T.
Proof.
  intros i j Γ A A' B B' ρ ρ' HE HA (a & a' & Ha & Ha' & R & HT) HB.
  destruct (HA _ _ HE) as (b & b' & Hb & Hb' & Q & HQ); resolve_eval.
  pose proof (at_type_coherent_l _ _ _ _ _ _ _ HT HQ) as HX.
  destruct (choose_family j R ρ B ρ' B') as (T & HC & Hcod).
  {
    intros x x' Hx.
    assert (HE' : env_related (A :: Γ) (extend_env ρ x) (extend_env ρ' x')).
    { eapply env_related_extend; [exact HE | exact Ha | exact Hb' | exists i; exact HQ | now apply HX]. }
    destruct (HB _ _ HE') as (c & c' & Hc & Hc' & V & HV).
    exists c, c', V; tauto.
  }
  exists a, a', R, T; repeat split; assumption.
Qed.

Lemma semantic_pi_codes : forall Γ i A A' B B',
    kind_at i Γ A ->
    exp_related Γ (a_typ i) A A' ->
    exp_related (A :: Γ) (a_typ i) B B' ->
    exp_related Γ (a_typ i) (a_pi A B) (a_pi A' B').
Proof.
  intros Γ i A A' B B' HA HEA HEB ρ ρ' HE.
  destruct (prepare_binder i i Γ A A' B B' _ _ HE HA
              (from_universe _ _ _ _ _ (HEA _ _ HE))) as (a & a' & R & T & Ha & Ha' & HT & HC & Hcod).
  { intros; now apply from_universe, HEB. }
  apply at_universe.
  exists (d_pi a ρ B), (d_pi a' ρ' B'); repeat split; try (now apply eval_exp_pi).
  exists (pi_rel R T); now apply model_pi.
Qed.

Lemma semantic_sigma_codes : forall Γ i A A' B B',
    kind_at i Γ A ->
    exp_related Γ (a_typ i) A A' ->
    exp_related (A :: Γ) (a_typ i) B B' ->
    exp_related Γ (a_typ i) (a_sigma A B) (a_sigma A' B').
Proof.
  intros Γ i A A' B B' HA HEA HEB ρ ρ' HE.
  destruct (prepare_binder i i Γ A A' B B' _ _ HE HA
              (from_universe _ _ _ _ _ (HEA _ _ HE))) as (a & a' & R & T & Ha & Ha' & HT & HC & Hcod).
  { intros; now apply from_universe, HEB. }
  apply at_universe.
  exists (d_sigma a ρ B), (d_sigma a' ρ' B'); repeat split; try (now apply eval_exp_sigma).
  exists (sigma_rel R T); now apply model_sigma.
Qed.

Lemma kind_pi : forall i Γ A B,
    kind_at i Γ A -> kind_at i (A :: Γ) B -> kind_at i Γ (a_pi A B).
Proof.
  intros i Γ A B HA HB; apply kind_from_typing.
  apply semantic_pi_codes; [exact HA | |]; intros ρ ρ' HE; apply at_universe; auto.
Qed.

Lemma kind_sigma : forall i Γ A B,
    kind_at i Γ A -> kind_at i (A :: Γ) B -> kind_at i Γ (a_sigma A B).
Proof.
  intros i Γ A B HA HB; apply kind_from_typing.
  apply semantic_sigma_codes; [exact HA | |]; intros ρ ρ' HE; apply at_universe; auto.
Qed.

Lemma semantic_lambda : forall Γ i j A A' B M N,
    kind_at i Γ A ->
    exp_related Γ (a_typ i) A A' ->
    kind_at j (A :: Γ) B ->
    exp_related (A :: Γ) B M N ->
    exp_related Γ (a_pi A B) (a_fn A M) (a_fn A' N).
Proof.
  intros Γ i j A A' B M N HA HEA HB HM ρ ρ' HE.
  destruct (prepare_binder i j Γ A A B B ρ ρ' HE HA (HA _ _ HE) HB)
    as (a & a' & R & T & Ha & Ha' & HT & HC & HB').
  exists (pi_rel R T); split.
  - exists (d_pi a ρ B), (d_pi a' ρ' B); repeat split; try (now apply eval_exp_pi).
    exists (Nat.max i j). apply model_pi.
    + eapply model_type_lift; [apply Nat.le_max_l | exact HT].
    + exact HC.
    + intros x x' Hx b b' Hb Hb'.
      eapply model_type_lift; [apply Nat.le_max_r | exact (HB' _ _ Hx _ _ Hb Hb')].
  - exists (d_fn ρ M), (d_fn ρ' N); split; [apply eval_exp_fn | split; [apply eval_exp_fn |]].
    intros x x' Hx.
    assert (HE' : env_related (A :: Γ) (extend_env ρ x) (extend_env ρ' x')).
    { eapply env_related_extend; [exact HE | exact Ha | exact Ha' | exists i; exact HT | exact Hx]. }
    destruct (HM _ _ HE') as (Q & (b & b' & Hb & Hb' & HQ) & m & n & Hm & Hn & Hmn).
    pose proof (type_values_equiv_l _ _ _ _ _ HQ (ex_intro _ j (HB' _ _ Hx _ _ Hb Hb'))) as HX.
    exists m, n; repeat split; try (now apply eval_app_fn); now apply HX.
Qed.

Lemma exp_related_self : forall Γ A M N, exp_related Γ A M N -> exp_related Γ A M M.
Proof. eauto using exp_related_trans, exp_related_sym. Qed.

Lemma eval_pair_cast : forall ρ ρ' A M N R,
    exp_related_at ρ ρ' A M N -> type_pair ρ ρ' A A R -> eval_pair ρ ρ' M N R.
Proof.
  intros ρ ρ' A M N R (T & HT & m & n & Hm & Hn & HR) HQ.
  pose proof (type_pair_coherent_l _ _ _ _ _ _ _ _ HT HQ) as HX.
  exists m, n; repeat split; try assumption; now apply HX.
Qed.

Lemma semantic_id : forall Γ, sub_related Γ Γ a_id a_id.
Proof. intros Γ ρ ρ' HE; exists ρ, ρ'; repeat split; try assumption; constructor. Qed.
Lemma semantic_weaken : forall Γ A, sub_related (A :: Γ) Γ a_weaken a_weaken.
Proof. intros Γ A ρ ρ' [HE _]; exists (drop_env ρ), (drop_env ρ'); repeat split; try assumption; constructor. Qed.
Lemma semantic_compose : forall Γ Δ Θ σ σ' τ τ',
    sub_related Γ Δ τ τ' -> sub_related Δ Θ σ σ' ->
    sub_related Γ Θ (a_compose σ τ) (a_compose σ' τ').
Proof.
  intros Γ Δ Θ σ σ' τ τ' Hτ Hσ ρ ρ' HE.
  destruct (Hτ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  destruct (Hσ _ _ HD) as (η & η' & Hη & Hη' & HH).
  exists η, η'; repeat split; try assumption; eapply eval_sub_compose; eassumption.
Qed.
Lemma semantic_extend : forall Γ Δ A σ τ M M' i,
    sub_related Γ Δ σ τ -> kind_at i Δ A -> exp_related Γ (a_sub A σ) M M' ->
    sub_related Γ (A :: Δ) (a_extend σ M) (a_extend τ M').
Proof.
  intros Γ Δ A σ τ M M' i Hσ HA HM ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  destruct (sub_related_self_l _ _ _ _ Hσ _ _ HE) as (χ & χ' & Hχ & Hχ' & HC).
  destruct (HA _ _ HD) as (a & a' & Ha & Ha' & R & HR).
  destruct (HA _ _ HC) as (c & c' & Hc & Hc' & T & HT).
  resolve_eval.
  assert (Htype : type_pair ρ ρ' (a_sub A σ) (a_sub A σ) T).
  { exists a, c'; repeat split; try (eapply eval_exp_sub; eassumption); now exists i. }
  destruct (eval_pair_cast _ _ _ _ _ _ (HM _ _ HE) Htype)
    as (m & m' & Hm & Hm' & Hrel).
  pose proof (at_type_coherent_l _ _ _ _ _ _ _ HT HR) as HX.
  exists (extend_env θ m), (extend_env θ' m'); split; [|split].
  - eapply eval_sub_extend; eassumption.
  - eapply eval_sub_extend; eassumption.
  - eapply env_related_extend; [exact HD | exact Ha | exact Ha' | exists i; exact HR | now apply HX].
Qed.
Lemma semantic_cons : forall Γ A M N i,
    kind_at i Γ A -> exp_related Γ A M N ->
    sub_related Γ (A :: Γ) (a_extend a_id M) (a_extend a_id N).
Proof.
  intros Γ A M N i HA HM ρ ρ' HE.
  destruct (HA _ _ HE) as (a & a' & Ha & Ha' & R & HR).
  assert (HT : type_pair ρ ρ' A A R) by (exists a, a'; repeat split; try assumption; now exists i).
  destruct (eval_pair_cast _ _ _ _ _ _ (HM _ _ HE) HT) as (m & n & Hm & Hn & Hmn).
  exists (extend_env ρ m), (extend_env ρ' n); split; [|split].
  - apply eval_sub_extend; [constructor | exact Hm].
  - apply eval_sub_extend; [constructor | exact Hn].
  - eapply env_related_extend; [exact HE | exact Ha | exact Ha' | exists i; exact HR | exact Hmn].
Qed.

Lemma semantic_application : forall Γ A B M M' N N',
    exp_related Γ (a_pi A B) M M' -> exp_related Γ A N N' ->
    exp_related Γ (a_sub B (a_extend a_id N)) (a_app M N) (a_app M' N').
Proof.
  intros Γ A B M M' N N' HM HN ρ ρ' HE.
  destruct (HM _ _ HE) as (V & (fT & fT' & HfT & HfT' & [i HT]) & f & f' & Hf & Hf' & HV).
  inversion HfT; inversion HfT'; subst; clear HfT HfT'.
  apply model_type_view in HT; cbn in HT; destruct HT as (R & T & HR & HC & HB & HX).
  assert (HA : type_pair ρ ρ' A A R) by (eexists _, _; repeat split; try eassumption; now exists i).
  destruct (eval_pair_cast _ _ _ _ _ _ (HN _ _ HE) HA) as (m & m' & Hm & Hm' & Hmrel).
  destruct (eval_pair_cast _ _ _ _ _ _ (exp_related_self _ _ _ _ HN _ _ HE) HA)
    as (x & x' & Hx & Hx' & Hxrel).
  pose proof (exp_unique _ _ _ Hx _ Hm) as E; subst x.
  destruct (proj2 (HX _ _) HV _ _ Hmrel) as (y & y' & Hy & Hy' & Hrel).
  destruct (HC _ _ Hmrel) as (b & b' & Hb & Hb').
  destruct (HC _ _ Hxrel) as (c & c' & Hc & Hc'); pose proof (exp_unique _ _ _ Hc _ Hb) as E; subst c.
  pose proof (at_type_coherent_l _ _ _ _ _ _ _
      (HB _ _ Hmrel _ _ Hb Hb') (HB _ _ Hxrel _ _ Hb Hc')) as HT.
  exists (T m x'); split.
  - exists b, c'; split; [|split].
    + eapply eval_exp_sub; [apply eval_sub_extend; [apply eval_sub_id | exact Hm] | exact Hb].
    + eapply eval_exp_sub; [apply eval_sub_extend; [apply eval_sub_id | exact Hx'] | exact Hc'].
    + exists i; exact (HB _ _ Hxrel _ _ Hb Hc').
  - exists y, y'; split; [|split].
    + eapply eval_exp_app; eassumption.
    + eapply eval_exp_app; eassumption.
    + now apply HT.
Qed.

Lemma semantic_pair : forall Γ A B A' B' M M' N N' i,
    kind_at i Γ A -> kind_at i (A :: Γ) B ->
    exp_related Γ A M M' -> exp_related Γ (a_sub B (a_extend a_id M)) N N' ->
    exp_related Γ (a_sigma A B) (a_pair M A N B) (a_pair M' A' N' B').
Proof.
  intros Γ A B A' B' M M' N N' i HA HB HM HN ρ ρ' HE.
  destruct (prepare_binder i i Γ A A B B ρ ρ' HE HA (HA _ _ HE) HB)
    as (a & a' & R & T & Ha & Ha' & HT & HC & Hcod).
  assert (Htype : type_pair ρ ρ' A A R) by
     (exists a, a'; repeat split; try assumption; now exists i).
  destruct (eval_pair_cast _ _ _ _ _ _ (HM _ _ HE) Htype) as (m & m' & Hm & Hm' & Hrel).
  destruct (HN _ _ HE) as (NR & (b & b' & Hb & Hb' & HBT) & n & n' & Hn & Hn' & HNR).
  destruct (HC _ _ Hrel) as (c & c' & Hc & Hc').
  assert (HEc : eval_exp (a_sub B (a_extend a_id M)) ρ c) by
    (eapply eval_exp_sub; [apply eval_sub_extend; [apply eval_sub_id | exact Hm] | exact Hc]).
  resolve_eval.
  pose proof (type_values_equiv_l _ _ _ _ _ HBT (ex_intro _ i (Hcod _ _ Hrel _ _ Hc Hc'))) as HX.
  exists (sigma_rel R T); split.
  - exists (d_sigma a ρ B), (d_sigma a' ρ' B).
    repeat split; try (now apply eval_exp_sigma).
    exists i; now apply model_sigma.
  - exists (d_pair m n), (d_pair m' n'); split; [|split].
    + now apply eval_exp_pair.
    + now apply eval_exp_pair.
    + exists m, m', n, n'; repeat split; try constructor; try assumption; now apply HX.
Qed.

Lemma semantic_fst : forall Γ A B M M',
    exp_related Γ (a_sigma A B) M M' -> exp_related Γ A (a_fst M) (a_fst M').
Proof.
  intros Γ A B M M' HM ρ ρ' HE.
  destruct (HM _ _ HE) as (V & (pT & pT' & HpT & HpT' & [i HT]) & p & p' & Hp & Hp' & HV).
  inversion HpT; inversion HpT'; subst; clear HpT HpT'.
  apply model_type_view in HT; cbn in HT; destruct HT as (R & T & HR & HC & HB & HX).
  destruct (proj2 (HX _ _) HV) as (x & x' & y & y' & Hx & Hx' & Hy & Hy' & Hxrel & Hyrel).
  exists R; split.
  - eexists _, _; repeat split; try eassumption; now exists i.
  - exists x, x'; repeat split; try assumption; eapply eval_exp_fst; eassumption.
Qed.

Lemma semantic_snd : forall Γ A B M M',
    exp_related Γ (a_sigma A B) M M' ->
    exp_related Γ (a_sub B (a_extend a_id (a_fst M))) (a_snd M) (a_snd M').
Proof.
  intros Γ A B M M' HM ρ ρ' HE.
  destruct (HM _ _ HE) as (V & (pT & pT' & HpT & HpT' & [i HT]) & p & p' & Hp & Hp' & HV).
  inversion HpT; inversion HpT'; subst; clear HpT HpT'.
  apply model_type_view in HT; cbn in HT; destruct HT as (R & T & HR & HC & HB & HX).
  destruct (proj2 (HX _ _) HV) as (x & x' & y & y' & Hx & Hx' & Hy & Hy' & Hxrel & Hyrel).
  assert (HA : type_pair ρ ρ' A A R) by (eexists _, _; repeat split; try eassumption; now exists i).
  destruct (eval_pair_cast _ _ _ _ _ _ (semantic_fst _ _ _ _ _ (exp_related_self _ _ _ _ HM) _ _ HE) HA)
    as (z & z' & Hz & Hz' & Hzrel).
  assert (HEx : eval_exp (a_fst M) ρ x) by (eapply eval_exp_fst; eassumption).
  pose proof (exp_unique _ _ _ Hz _ HEx) as E; subst z.
  destruct (HC _ _ Hxrel) as (b & b' & Hb & Hb').
  destruct (HC _ _ Hzrel) as (c & c' & Hc & Hc'); pose proof (exp_unique _ _ _ Hc _ Hb) as E; subst c.
  pose proof (at_type_coherent_l _ _ _ _ _ _ _
    (HB _ _ Hxrel _ _ Hb Hb') (HB _ _ Hzrel _ _ Hb Hc')) as HCoh.
  exists (T x z'); split.
  - exists b, c'; split; [|split].
    + eapply eval_exp_sub; [apply eval_sub_extend; [apply eval_sub_id | exact HEx] | exact Hb].
    + eapply eval_exp_sub; [apply eval_sub_extend; [apply eval_sub_id | exact Hz'] | exact Hc'].
    + exists i; exact (HB _ _ Hzrel _ _ Hb Hc').
  - exists y, y'; split; [|split].
    + eapply eval_exp_snd; eassumption.
    + eapply eval_exp_snd; eassumption.
    + now apply HCoh.
Qed.

Lemma semantic_eq_codes : forall Γ i A A' M M' N N',
    exp_related Γ (a_typ i) A A' ->
    exp_related Γ A M M' -> exp_related Γ A N N' ->
    exp_related Γ (a_typ i) (a_eq A M N) (a_eq A' M' N').
Proof.
  intros Γ i A A' M M' N N' HA HM HN ρ ρ' HE.
  destruct (from_universe _ _ _ _ _ (HA _ _ HE)) as (a & a' & Ha & Ha' & R & HR).
  destruct (HM _ _ HE) as (T & HT & m & m' & Hm & Hm' & Hmr).
  destruct (HN _ _ HE) as (V & HV & n & n' & Hn & Hn' & Hnr).
  assert (HX : type_pair ρ ρ' A A' R) by (exists a, a'; repeat split; try assumption; now exists i).
  pose proof (type_pair_coherent_l _ _ _ _ _ _ _ _ HT HX) as HT'.
  pose proof (type_pair_coherent_l _ _ _ _ _ _ _ _ HV HX) as HV'.
  apply at_universe.
  exists (d_eq a m n), (d_eq a' m' n'); repeat split; try (apply eval_exp_eq; assumption).
  exists (eq_rel R m n m' n'). apply model_eq; [exact HR | now apply HT' | now apply HV'].
Qed.

Lemma kind_eq : forall i Γ A M N,
    kind_at i Γ A -> exp_related Γ A M M -> exp_related Γ A N N ->
    kind_at i Γ (a_eq A M N).
Proof.
  intros i Γ A M N HA HM HN; apply kind_from_typing.
  apply semantic_eq_codes; try assumption.
  intros ρ ρ' HE; apply at_universe; auto.
Qed.

Lemma semantic_refl : forall Γ i A A' M M',
    kind_at i Γ A -> exp_related Γ A M M' ->
    exp_related Γ (a_eq A M M) (a_refl A M) (a_refl A' M').
Proof.
  intros Γ i A A' M M' HA HM ρ ρ' HE.
  destruct (HA _ _ HE) as (a & a' & Ha & Ha' & R & HR).
  assert (HX : type_pair ρ ρ' A A R) by (exists a, a'; repeat split; try assumption; now exists i).
  destruct (eval_pair_cast _ _ _ _ _ _ (HM _ _ HE) HX) as (m & n & Hm & Hn & Hmn).
  destruct (eval_pair_cast _ _ _ _ _ _ (exp_related_self _ _ _ _ HM _ _ HE) HX)
    as (m' & n' & Hm' & Hn' & Hmn').
  pose proof (exp_unique _ _ _ Hm' _ Hm) as E; subst m'.
  exists (eq_rel R m m n' n'); split.
  - exists (d_eq a m m), (d_eq a' n' n'); repeat split; try (apply eval_exp_eq; assumption).
    exists i; now apply model_eq.
  - exists (d_refl m), (d_refl n); repeat split; try (now apply eval_exp_refl).
    apply eq_rel_refl; assumption.
Qed.

Lemma semantic_zero : forall Γ, exp_related Γ a_nat a_zero a_zero.
Proof. intros Γ ρ ρ' HE; apply at_nat; exists d_zero, d_zero; repeat split; constructor. Qed.
Lemma semantic_succ : forall Γ M N, exp_related Γ a_nat M N ->
    exp_related Γ a_nat (a_succ M) (a_succ N).
Proof.
  intros Γ M N H ρ ρ' HE.
  destruct (from_nat _ _ _ _ (H _ _ HE)) as (m & n & Hm & Hn & HR).
  apply at_nat; exists (d_succ m), (d_succ n); repeat split; now constructor.
Qed.
Lemma semantic_natural_type : forall Γ, exp_related Γ (a_typ 0) a_nat a_nat.
Proof. intros Γ ρ ρ' HE; apply at_universe; exact (kind_nat Γ _ _ HE). Qed.
Lemma semantic_universe : forall Γ i, exp_related Γ (a_typ (S i)) (a_typ i) (a_typ i).
Proof. intros Γ i ρ ρ' HE; apply at_universe; exact (kind_universe i Γ _ _ HE). Qed.


Lemma nat_model_eliminate : forall i R ρ ρ' B B' Z Z' Suc Suc' z z',
    closures nat_rel ρ B ρ' B' ->
    model_codomains (universes i) nat_rel ρ B ρ' B' R ->
    eval_exp Z ρ z -> eval_exp Z' ρ' z' -> R d_zero d_zero z z' ->
    (forall m m', nat_rel m m' -> forall x x', R m m' x x' ->
        exists y y',
          eval_exp Suc (extend_env (extend_env ρ m) x) y /\
          eval_exp Suc' (extend_env (extend_env ρ' m') x') y' /\
          R (d_succ m) (d_succ m') y y') ->
    forall m m', nat_rel m m' ->
      exists y y', eval_natrec B Z Suc m ρ y /\ eval_natrec B' Z' Suc' m' ρ' y' /\ R m m' y y'.
Proof.
  intros i R ρ ρ' B B' Z Z' Suc Suc' z z' HC HT HZ HZ' HR Hz m m' Hm.
  induction Hm as [|m m' Hm IH|a a' n n' Hn].
  - exists z, z'; repeat split; try assumption; now constructor.
  - destruct IH as (x & x' & Hx & Hx' & Hxr).
    destruct (Hz _ _ Hm _ _ Hxr) as (y & y' & Hy & Hy' & Hyr).
    exists y, y'; repeat split; try assumption; eapply eval_natrec_succ; eassumption.
  - pose proof (nat_rel_neut a a' n n' Hn) as Hnn.
    destruct (HC _ _ Hnn) as (b & b' & Hb & Hb').
    destruct (model_readback _ (universes_valid i) _ _ _ (HT _ _ Hnn _ _ Hb Hb')) as [_ [_ Hreflect]].
    exists (d_neut b (d_natrec ρ B z Suc n)), (d_neut b' (d_natrec ρ' B' z' Suc' n')).
    split; [|split].
    + now apply eval_natrec_neut.
    + now apply eval_natrec_neut.
    + apply Hreflect. intros s.
      set (v := d_neut d_nat (d_var s)).
      assert (Hv : nat_rel v v) by (apply nat_rel_neut, ne_related_var).
      destruct (HC _ _ Hv) as (c & c' & Hc & Hc').
      destruct (model_readback _ (universes_valid i) _ _ _ (HT _ _ Hv _ _ Hc Hc'))
        as [HCread [_ HCreflect]].
      destruct (HCread (S s)) as (C & HCr & HCr').
      destruct (HC _ _ nat_rel_zero) as (b0 & b0' & Hb0 & Hb0').
      destruct (model_readback _ (universes_valid i) _ _ _ (HT _ _ nat_rel_zero _ _ Hb0 Hb0'))
        as [_ [HZread _]].
      destruct (HZread _ _ HR s) as (NFZ & HZr & HZr').
      pose proof (nat_rel_succ _ _ Hv) as Hvs.
      destruct (HC _ _ Hvs) as (bS & bS' & HbS & HbS').
      destruct (model_readback _ (universes_valid i) _ _ _ (HT _ _ Hvs _ _ HbS HbS'))
        as [_ [HSread _]].
      pose proof (HCreflect _ _ (ne_related_var (S s))) as Hrec.
      destruct (Hz _ _ Hv _ _ Hrec) as (r & r' & Hr & Hr' & Hrr).
      destruct (HSread _ _ Hrr (S (S s))) as (NFS & HSr & HSr').
      destruct (Hn s) as (N & HNr & HNr').
      exists (ne_natrec C NFZ NFS N); split; eapply read_ne_natrec; eassumption.
Qed.

Lemma semantic_natrec : forall Γ i A A' Z Z' Suc Suc' M M',
    kind_at i (a_nat :: Γ) A ->
    exp_related (a_nat :: Γ) (a_typ i) A A' ->
    exp_related Γ (a_sub A (a_extend a_id a_zero)) Z Z' ->
    exp_related (A :: a_nat :: Γ) (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc Suc' ->
    exp_related Γ a_nat M M' ->
    exp_related Γ (a_sub A (a_extend a_id M)) (a_natrec A Z Suc M) (a_natrec A' Z' Suc' M').
Proof.
  intros Γ i A A' Z Z' Suc Suc' M M' HA HAA HZ HS HM ρ ρ' HE.
  assert (env_nat : forall x x', nat_rel x x' ->
    env_related (a_nat :: Γ) (extend_env ρ x) (extend_env ρ' x')).
  {
    intros x x' Hx; eapply env_related_extend; [exact HE | constructor | constructor | | exact Hx].
    exists 0; apply model_nat.
  }
  destruct (choose_family i nat_rel ρ A ρ' A') as (R & HC & HT).
  {
    intros x x' Hx.
    destruct (from_universe _ _ _ _ _ (HAA _ _ (env_nat _ _ Hx))) as (a & a' & Ha & Ha' & RR & HR).
    exists a, a', RR; tauto.
  }
  destruct (HZ _ _ HE) as (ZR & (a0 & a0' & Ha0 & Ha0' & HZR) & z & z' & Hz & Hz' & Hzz).
  destruct (HC _ _ nat_rel_zero) as (b0 & b0' & Hb0 & Hb0').
  assert (Hb0sub : eval_exp (a_sub A (a_extend a_id a_zero)) ρ b0).
  { eapply eval_exp_sub; [apply eval_sub_extend; constructor | exact Hb0]. }
  pose proof (exp_unique _ _ _ Ha0 _ Hb0sub) as E; subst a0.
  pose proof (type_values_equiv_l _ _ _ _ _ HZR
    (ex_intro _ i (HT _ _ nat_rel_zero _ _ Hb0 Hb0'))) as HEX.
  assert (Hstep : forall m m', nat_rel m m' -> forall x x', R m m' x x' ->
    exists y y', eval_exp Suc (extend_env (extend_env ρ m) x) y /\
                 eval_exp Suc' (extend_env (extend_env ρ' m') x') y' /\
                 R (d_succ m) (d_succ m') y y').
  {
    intros m m' Hm x x' Hx.
    destruct (HA _ _ (env_nat _ _ Hm)) as (a & a' & Ha & Ha' & AR & HAr).
    destruct (HC _ _ Hm) as (b & b' & Hb & Hb').
    pose proof (exp_unique _ _ _ Hb _ Ha) as Eb; subst b.
    pose proof (at_type_coherent_l _ _ _ _ _ _ _ (HT _ _ Hm _ _ Ha Hb') HAr) as Hcast.
    assert (Henv : env_related (A :: a_nat :: Γ)
      (extend_env (extend_env ρ m) x) (extend_env (extend_env ρ' m') x')).
    { eapply env_related_extend; [apply env_nat; exact Hm | exact Ha | exact Ha' | exists i; exact HAr | now apply Hcast]. }
    destruct (HS _ _ Henv) as (RR & (c & c' & Hc & Hc' & HCr) & y & y' & Hy & Hy' & Hyr).
    pose proof (nat_rel_succ _ _ Hm) as Hsm.
    destruct (HC _ _ Hsm) as (d & d' & Hd & Hd').
    assert (Hsim : eval_exp (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1))))
                   (extend_env (extend_env ρ m) x) d).
    { eapply eval_exp_sub; [|exact Hd].
      apply eval_sub_extend; [eapply eval_sub_compose; constructor | apply eval_exp_succ, eval_exp_var]. }
    pose proof (exp_unique _ _ _ Hc _ Hsim) as Ec; subst c.
    pose proof (type_values_equiv_l _ _ _ _ _ HCr (ex_intro _ i (HT _ _ Hsm _ _ Hd Hd'))) as Hout.
    exists y, y'; repeat split; try assumption; now apply Hout.
  }
  destruct (from_nat _ _ _ _ (HM _ _ HE)) as (m & m' & Hm & Hm' & Hmr).
  destruct (nat_model_eliminate i R ρ ρ' A A' Z Z' Suc Suc' z z'
    HC HT Hz Hz' (proj1 (HEX _ _) Hzz) Hstep _ _ Hmr)
    as (v & v' & Hv & Hv' & Hvr).
  destruct (from_nat _ _ _ _ (exp_related_self _ _ _ _ HM _ _ HE))
    as (n & n' & Hn & Hn' & Hnr).
  pose proof (exp_unique _ _ _ Hn _ Hm) as En; subst n.
  destruct (HA _ _ (env_nat _ _ Hnr)) as (a & a' & Ha & Ha' & AR & HAr).
  destruct (HC _ _ Hmr) as (b & b' & Hb & Hb').
  pose proof (exp_unique _ _ _ Hb _ Ha) as Eb; subst b.
  pose proof (at_type_coherent_l _ _ _ _ _ _ _ (HT _ _ Hmr _ _ Ha Hb') HAr) as Hcast.
  exists AR; split.
  - exists a, a'; split; [|split].
    + eapply eval_exp_sub; [apply eval_sub_extend; [constructor | exact Hm] | exact Ha].
    + eapply eval_exp_sub; [apply eval_sub_extend; [constructor | exact Hn'] | exact Ha'].
    + exists i; exact HAr.
  - exists v, v'; split; [|split].
    + eapply eval_exp_natrec; eassumption.
    + eapply eval_exp_natrec; eassumption.
    + now apply Hcast.
Qed.

Lemma related_subtype_families : forall Γ i A A' B B' ρ ρ',
    env_related Γ ρ ρ' ->
    kind_at i Γ A -> kind_at i Γ A' ->
    exp_related Γ (a_typ i) A A' ->
    kind_at i (A :: Γ) B -> kind_at i (A' :: Γ) B' ->
    subtype_related (A' :: Γ) B B' ->
    exists a a' c c' R T T',
      eval_exp A ρ a /\ eval_exp A ρ' a' /\ eval_exp A' ρ c /\ eval_exp A' ρ' c' /\
      at_type i a a' R /\ at_type i c c' R /\
      closures R ρ B ρ' B /\ closures R ρ B' ρ' B' /\
      model_codomains (universes i) R ρ B ρ' B T /\
      model_codomains (universes i) R ρ B' ρ' B' T' /\
      (forall x x', R x x' -> includes (T x x') (T' x x')).
Proof.
  intros Γ i A A' B B' ρ ρ' HE HA HA' HEA HB HB' HS.
  destruct (prepare_binder i i Γ A A B B ρ ρ' HE HA (HA _ _ HE) HB)
    as (a & a' & R & T & Ha & Ha' & HR & HC & Hcod).
  destruct (HA' _ _ HE) as (c & c' & Hc & Hc' & Q & HQ).
  destruct (from_universe _ _ _ _ _ (HEA _ _ HE)) as (b & b' & Hb & Hb' & V & HV).
  pose proof (exp_unique _ _ _ Hb _ Ha) as ->.
  pose proof (exp_unique _ _ _ Hb' _ Hc') as ->.
  pose proof (at_type_coherent_l _ _ _ _ _ _ _ HV HR) as HER.
  pose proof (at_type_coherent_r _ _ _ _ _ _ _ HV HQ) as HEQ.
  assert (HTQ : at_type i c c' R).
  { eapply model_ext; [exact HQ |]. eapply equiv_trans; [apply equiv_sym; exact HEQ | exact HER]. }
  assert (Henv : forall x x', R x x' -> env_related (A' :: Γ) (extend_env ρ x) (extend_env ρ' x')).
  { intros x x' Hx; eapply env_related_extend; [exact HE | exact Hc | exact Hc' | exists i; exact HTQ | exact Hx]. }
  destruct (choose_family i R ρ B' ρ' B') as (T' & HC' & Hcod').
  {
    intros x x' Hx. destruct (HB' _ _ (Henv _ _ Hx)) as (d & d' & Hd & Hd' & S & HSt).
    exists d, d', S; tauto.
  }
  exists a, a', c, c', R, T, T'; repeat split; try assumption.
  intros x x' Hx y y' Hy.
  destruct (HS _ _ (Henv _ _ Hx)) as
    (RA & RB & (v & v' & Hv & Hv' & HAsem) & (w & w' & Hw & Hw' & HBsem) & Hsub).
  pose proof (type_values_equiv_l _ _ _ _ _ HAsem
    (ex_intro _ i (Hcod _ _ Hx _ _ Hv Hv'))) as HAeq.
  pose proof (type_values_equiv_l _ _ _ _ _ HBsem
    (ex_intro _ i (Hcod' _ _ Hx _ _ Hw Hw'))) as HBeq.
  apply HBeq, Hsub, HAeq, Hy.
Qed.

Lemma semantic_subtype_pi : forall Γ i A A' B B',
    kind_at i Γ A -> kind_at i Γ A' -> exp_related Γ (a_typ i) A A' ->
    kind_at i (A :: Γ) B -> kind_at i (A' :: Γ) B' ->
    subtype_related (A' :: Γ) B B' ->
    subtype_related Γ (a_pi A B) (a_pi A' B').
Proof.
  intros Γ i A A' B B' HA HA' HEA HB HB' HS ρ ρ' HE.
  destruct (related_subtype_families Γ i A A' B B' _ _ HE HA HA' HEA HB HB' HS)
    as (a & a' & c & c' & R & T & T' & Ha & Ha' & Hc & Hc' & HR & HR' & HC & HC' & HT & HT' & HI).
  exists (pi_rel R T), (pi_rel R T'); split; [|split].
  - exists (d_pi a ρ B), (d_pi a' ρ' B); split; [now apply eval_exp_pi | split; [now apply eval_exp_pi |]].
    exists i; now apply model_pi.
  - exists (d_pi c ρ B'), (d_pi c' ρ' B'); split; [now apply eval_exp_pi | split; [now apply eval_exp_pi |]].
    exists i; now apply model_pi.
  - intros f f' HF x x' Hx.
    destruct (HF _ _ Hx) as (y & y' & Hy & Hy' & HRy).
    exists y, y'; repeat split; try assumption.
    exact (HI _ _ Hx _ _ HRy).
Qed.

Lemma semantic_subtype_sigma : forall Γ i A A' B B',
    kind_at i Γ A -> kind_at i Γ A' -> exp_related Γ (a_typ i) A A' ->
    kind_at i (A :: Γ) B -> kind_at i (A' :: Γ) B' ->
    subtype_related (A' :: Γ) B B' ->
    subtype_related Γ (a_sigma A B) (a_sigma A' B').
Proof.
  intros Γ i A A' B B' HA HA' HEA HB HB' HS ρ ρ' HE.
  destruct (related_subtype_families Γ i A A' B B' _ _ HE HA HA' HEA HB HB' HS)
    as (a & a' & c & c' & R & T & T' & Ha & Ha' & Hc & Hc' & HR & HR' & HC & HC' & HT & HT' & HI).
  exists (sigma_rel R T), (sigma_rel R T'); split; [|split].
  - exists (d_sigma a ρ B), (d_sigma a' ρ' B); split; [now apply eval_exp_sigma | split; [now apply eval_exp_sigma |]].
    exists i; now apply model_sigma.
  - exists (d_sigma c ρ B'), (d_sigma c' ρ' B'); split; [now apply eval_exp_sigma | split; [now apply eval_exp_sigma |]].
    exists i; now apply model_sigma.
  - intros p p' (x & x' & y & y' & Hx & Hx' & Hy & Hy' & HRx & HRy).
    exists x, x', y, y'; repeat split; try assumption.
    exact (HI _ _ HRx _ _ HRy).
Qed.

Definition extend_three ρ x y z := extend_env (extend_env (extend_env ρ x) y) z.

Definition equality_motives i R ρ B ρ' B' :=
  forall x y p x' y' p', R x x' -> R y y' -> eq_rel R x y x' y' p p' ->
    exists b b' T,
       eval_exp B (extend_three ρ x y p) b /\
       eval_exp B' (extend_three ρ' x' y' p') b' /\ at_type i b b' T.

Definition equality_branches i R ρ B BR ρ' B' BR' :=
  forall x x', R x x' ->
    exists b b' T r r',
      eval_exp B (extend_three ρ x x (d_refl x)) b /\
      eval_exp B' (extend_three ρ' x' x' (d_refl x')) b' /\
      at_type i b b' T /\ eval_exp BR (extend_env ρ x) r /\
      eval_exp BR' (extend_env ρ' x') r' /\ T r r'.

Lemma equality_model_eliminate : forall i j a a' R B B' BR BR' ρ ρ',
    at_type j a a' R ->
    equality_motives i R ρ B ρ' B' ->
    equality_branches i R ρ B BR ρ' B' BR' ->
    forall x y p x' y' p',
      R x x' -> R y y' -> eq_rel R x y x' y' p p' ->
      exists b b' T r r',
        eval_exp B (extend_three ρ x y p) b /\
        eval_exp B' (extend_three ρ' x' y' p') b' /\
        at_type i b b' T /\ eval_eqrec a B BR x y p ρ r /\
        eval_eqrec a' B' BR' x' y' p' ρ' r' /\ T r r'.
Proof.
  intros i j a a' R B B' BR BR' ρ ρ' HA HM HB x y p x' y' p' Hx Hy Hp.
  destruct (HM _ _ _ _ _ _ Hx Hy Hp) as (b & b' & T & Hb & Hb' & HT).
  destruct Hp as [z z' Hzz Hzx Hzy Hxz Hyz | c c' n n' Hn].
  - destruct (HB _ _ Hzz) as (c & c' & V & r & r' & Hc & Hc' & HV & Hr & Hr' & Hrel).
    assert (HP : eq_rel R z z x' y' (d_refl z) (d_refl z')) by now apply eq_rel_refl.
    destruct (HM _ _ _ _ _ _ Hzx Hzy HP) as (d & d' & Q & Hd & Hd' & HQ).
    pose proof (exp_unique _ _ _ Hd _ Hc) as E; subst d.
    pose proof (exp_unique _ _ _ Hd' _ Hb') as E; subst d'.
    pose proof (at_type_coherent_l _ _ _ _ _ _ _ HV HQ) as H1.
    pose proof (at_type_coherent_r _ _ _ _ _ _ _ HQ HT) as H2.
    exists b, b', T, r, r'; repeat split; try assumption; try (now apply eval_eqrec_refl).
    apply H2, H1, Hrel.
  - destruct (model_readback _ (universes_valid j) _ _ _ HA) as (Htype & Hterms & Hrefl).
    destruct (model_readback _ (universes_valid i) _ _ _ HT) as [_ [_ Hreflect]].
    exists b, b', T, (d_neut b (d_eqrec ρ a B BR x y n)), (d_neut b' (d_eqrec ρ' a' B' BR' x' y' n')).
    split; [exact Hb |]; split; [exact Hb' |]; split; [exact HT |].
    split; [now apply eval_eqrec_neut |]; split; [now apply eval_eqrec_neut |].
    apply Hreflect. intros s.
    destruct (Htype s) as (A & HAr & HAr').
    destruct (Hterms _ _ Hx s) as (X & HX & HX').
    destruct (Hterms _ _ Hy s) as (Y & HY & HY').
    destruct (Hn s) as (N & HN & HN').
    set (u := d_neut a (d_var s)).
    set (u' := d_neut a' (d_var s)).
    set (v := d_neut a (d_var (S s))).
    set (v' := d_neut a' (d_var (S s))).
    set (w := d_neut (d_eq a u v) (d_var (S (S s)))).
    set (w' := d_neut (d_eq a' u' v') (d_var (S (S s)))).
    assert (Hu : R u u') by (apply Hrefl, ne_related_var).
    assert (Hv : R v v') by (apply Hrefl, ne_related_var).
    assert (Hw : eq_rel R u v u' v' w w') by (apply eq_rel_neut, ne_related_var).
    destruct (HM _ _ _ _ _ _ Hu Hv Hw) as (d & d' & Q & Hd & Hd' & HQ).
    destruct (model_readback _ (universes_valid i) _ _ _ HQ) as [HDr _].
    destruct (HDr (S (S (S s)))) as (D & HD & HD').
    destruct (HB _ _ Hu) as (e & e' & V & r & r' & He & He' & HV & Hr & Hr' & Hrel).
    destruct (model_readback _ (universes_valid i) _ _ _ HV) as [_ [HTr _]].
    destruct (HTr _ _ Hrel (S s)) as (NF & HNF & HNF').
    exists (ne_eqrec A D NF X Y N).
    split; eapply read_ne_eqrec; eassumption.
Qed.

Definition equality_context Γ A :=
  a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0) ::
    a_sub A a_weaken :: A :: Γ.

Definition equality_branch_type A B :=
  a_sub B (a_extend (a_extend a_id (a_var 0)) (a_refl (a_sub A a_weaken) (a_var 0))).

Definition equality_result_type B M N P :=
  a_sub B (a_extend (a_extend (a_extend a_id M) N) P).

Lemma relate_equality_context : forall Γ A ρ ρ' a a' i R x y p x' y' p',
    env_related Γ ρ ρ' -> eval_exp A ρ a -> eval_exp A ρ' a' -> at_type i a a' R ->
    R x x' -> R y y' -> eq_rel R x y x' y' p p' ->
    env_related (equality_context Γ A) (extend_three ρ x y p) (extend_three ρ' x' y' p').
Proof.
  intros Γ A ρ ρ' a a' i R x y p x' y' p' HE Ha Ha' HT HRx HRy HRp.
  assert (HA : type_values a a' R) by (exists i; exact HT).
  assert (HX : env_related (A :: Γ) (extend_env ρ x) (extend_env ρ' x')) by
    (eapply env_related_extend; eassumption).
  assert (HY : env_related (a_sub A a_weaken :: A :: Γ)
    (extend_env (extend_env ρ x) y) (extend_env (extend_env ρ' x') y')).
  {
    eapply env_related_extend; [exact HX | | | exact HA | exact HRy];
      (eapply eval_exp_sub; [apply eval_sub_weaken | eassumption]).
  }
  assert (HEq : type_values (d_eq a x y) (d_eq a' x' y') (eq_rel R x y x' y')) by
    (exists i; now apply model_eq).
  unfold equality_context, extend_three.
  eapply env_related_extend; [exact HY | | | exact HEq | exact HRp];
    (apply eval_exp_eq; [|apply eval_exp_var|apply eval_exp_var]);
    (eapply eval_exp_sub; [eapply eval_sub_compose; constructor | eassumption]).
Qed.

Lemma eval_equality_branch_type : forall A B ρ x b,
    eval_exp B (extend_three ρ x x (d_refl x)) b ->
    eval_exp (equality_branch_type A B) (extend_env ρ x) b.
Proof.
  intros A B ρ x b HB; unfold equality_branch_type.
  eapply eval_exp_sub; [|exact HB].
  apply eval_sub_extend.
  - apply eval_sub_extend; [apply eval_sub_id | apply eval_exp_var].
  - apply eval_exp_refl, eval_exp_var.
Qed.

Lemma eval_equality_result_type : forall B M N P ρ x y p b,
    eval_exp M ρ x -> eval_exp N ρ y -> eval_exp P ρ p ->
    eval_exp B (extend_three ρ x y p) b ->
    eval_exp (equality_result_type B M N P) ρ b.
Proof.
  intros B M N P ρ x y p b HM HN HP HB; unfold equality_result_type.
  eapply eval_exp_sub; [| exact HB].
  apply eval_sub_extend; [apply eval_sub_extend; [apply eval_sub_extend; [apply eval_sub_id | exact HM] | exact HN] | exact HP].
Qed.

Lemma semantic_equality_evaluation : forall Γ i A ρ ρ' a a' R M M' N N' P P',
    env_related Γ ρ ρ' ->
    eval_exp A ρ a -> eval_exp A ρ' a' -> at_type i a a' R ->
    exp_related Γ A M M' -> exp_related Γ A N N' ->
    exp_related Γ (a_eq A M N) P P' ->
    exists x y p x' y' p',
      eval_exp M ρ x /\ eval_exp N ρ y /\ eval_exp P ρ p /\
      eval_exp M' ρ' x' /\ eval_exp N' ρ' y' /\ eval_exp P' ρ' p' /\
      R x x' /\ R y y' /\ eq_rel R x y x' y' p p'.
Proof.
  intros Γ i A ρ ρ' a a' R M M' N N' P P' HE Ha Ha' HT HM HN HP.
  assert (Htype : type_pair ρ ρ' A A R) by
    (exists a, a'; repeat split; try assumption; now exists i).
  destruct (eval_pair_cast _ _ _ _ _ _ (HM _ _ HE) Htype) as (x & x' & HX & HX' & HRx).
  destruct (eval_pair_cast _ _ _ _ _ _ (HN _ _ HE) Htype) as (y & y' & HY & HY' & HRy).
  destruct (eval_pair_cast _ _ _ _ _ _ (exp_related_self _ _ _ _ HM _ _ HE) Htype)
    as (u & u' & HU & HU' & HRu).
  destruct (eval_pair_cast _ _ _ _ _ _ (exp_related_self _ _ _ _ HN _ _ HE) Htype)
    as (v & v' & HV & HV' & HRv).
  pose proof (exp_unique _ _ _ HU _ HX) as E; subst u.
  pose proof (exp_unique _ _ _ HV _ HY) as E; subst v.
  assert (HPT : type_pair ρ ρ' (a_eq A M N) (a_eq A M N) (eq_rel R x y u' v')).
  {
    exists (d_eq a x y), (d_eq a' u' v'); split; [now apply eval_exp_eq |].
    split; [now apply eval_exp_eq | exists i; now apply model_eq].
  }
  destruct (eval_pair_cast _ _ _ _ _ _ (HP _ _ HE) HPT) as (p & p' & HP' & HP'' & HRp).
  exists x, y, p, x', y', p'; repeat split; try assumption.
  pose proof (at_type_per _ _ _ _ HT) as Hper.
  refine (proj1 (eq_rel_right R x y u' v' x' y' Hper _ _ p p') HRp).
  - eapply (proj2 Hper); [apply (proj1 Hper); exact HRu | exact HRx].
  - eapply (proj2 Hper); [apply (proj1 Hper); exact HRv | exact HRy].
Qed.

Lemma kind_equality_result : forall Γ i j A B M N P,
    kind_at i Γ A -> kind_at j (equality_context Γ A) B ->
    exp_related Γ A M M -> exp_related Γ A N N -> exp_related Γ (a_eq A M N) P P ->
    kind_at j Γ (equality_result_type B M N P).
Proof.
  intros Γ i j A B M N P HA HB HM HN HP ρ ρ' HE.
  destruct (HA _ _ HE) as (a & a' & Ha & Ha' & R & HT).
  destruct (semantic_equality_evaluation _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE Ha Ha' HT HM HN HP)
    as (x & y & p & x' & y' & p' & Hx & Hy & Hp & Hx' & Hy' & Hp' & HRx & HRy & HRp).
  pose proof (relate_equality_context _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE Ha Ha' HT HRx HRy HRp) as HC.
  destruct (HB _ _ HC) as (b & b' & Hb & Hb' & HTT).
  exists b, b'; repeat split; try assumption; eapply eval_equality_result_type; eassumption.
Qed.

Lemma semantic_eqrec : forall Γ i j A A' B B' BR BR' M M' N N' P P',
    kind_at i Γ A -> exp_related Γ (a_typ i) A A' ->
    kind_at j (equality_context Γ A) B ->
    exp_related (equality_context Γ A) (a_typ j) B B' ->
    exp_related (A :: Γ) (equality_branch_type A B) BR BR' ->
    exp_related Γ A M M' -> exp_related Γ A N N' -> exp_related Γ (a_eq A M N) P P' ->
    exp_related Γ (equality_result_type B M N P)
      (a_eqrec A B BR M N P) (a_eqrec A' B' BR' M' N' P').
Proof.
  intros Γ i j A A' B B' BR BR' M M' N N' P P' HA HAA HB HBB HBR HM HN HP ρ ρ' HE.
  destruct (HA _ _ HE) as (a & a0 & Ha & Ha0 & R & HT).
  destruct (from_universe _ _ _ _ _ (HAA _ _ HE)) as (c & a' & Hleft & Ha' & Srel & HS).
  pose proof (exp_unique _ _ _ Hleft _ Ha) as E; subst c.
  assert (HT' : at_type i a a' R) by
    (eapply model_ext; [exact HS | exact (at_type_coherent_l _ _ _ _ _ _ _ HS HT)]).
  assert (Hmot : equality_motives j R ρ B ρ' B').
  {
    intros x y p x' y' p' Hx Hy Hp.
    pose proof (relate_equality_context _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE Ha Ha0 HT Hx Hy Hp) as HC.
    destruct (from_universe _ _ _ _ _ (HBB _ _ HC)) as (b & b' & Hb & Hb' & Q & HQ).
    exists b, b', Q; tauto.
  }
  assert (Hbr : equality_branches j R ρ B BR ρ' B' BR').
  {
    intros x x' Hx.
    assert (Henv : env_related (A :: Γ) (extend_env ρ x) (extend_env ρ' x')).
    { eapply env_related_extend; [exact HE | exact Ha | exact Ha0 | exists i; exact HT | exact Hx]. }
    assert (HR : eq_rel R x x x' x' (d_refl x) (d_refl x')) by now apply eq_rel_refl.
    destruct (Hmot _ _ _ _ _ _ Hx Hx HR) as (b & b' & Q & Hb & Hb' & HQ).
    destruct (HBR _ _ Henv) as (V & (c & c' & Hc & Hc' & HV) & r & r' & Hr & Hr' & Hrr).
    pose proof (exp_unique _ _ _ Hc _ (eval_equality_branch_type _ _ _ _ _ Hb)) as E; subst c.
    exists b, b', Q, r, r'; repeat split; try assumption.
    eapply (type_values_equiv_l _ _ _ _ _ HV (ex_intro _ j HQ)); exact Hrr.
  }
  destruct (semantic_equality_evaluation _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE Ha Ha0 HT HM HN HP)
    as (x & y & p & x' & y' & p' & Hx & Hy & Hp & Hx' & Hy' & Hp' & HRx & HRy & HRp).
  destruct (equality_model_eliminate j i a a' R B B' BR BR' ρ ρ' HT' Hmot Hbr
    _ _ _ _ _ _ HRx HRy HRp) as (b & b' & Q & r & r' & Hb & Hb' & HQ & Hr & Hr' & HRr).
  assert (kind_bounded_target : kind_at j Γ (equality_result_type B M N P)).
  { eapply kind_equality_result; [exact HA | exact HB | eapply exp_related_self; exact HM |
      eapply exp_related_self; exact HN | eapply exp_related_self; exact HP]. }
  destruct (kind_bounded_target _ _ HE) as (d & d' & Hd & Hd' & T & HTT).
  assert (Hdb : eval_exp (equality_result_type B M N P) ρ b) by
    (eapply eval_equality_result_type; eassumption).
  pose proof (exp_unique _ _ _ Hd _ Hdb) as E; subst d.
  exists T; split.
  - exists b, d'; repeat split; try assumption; now exists j.
  - exists r, r'; split; [|split].
    + eapply eval_exp_eqrec; eassumption.
    + eapply eval_exp_eqrec; eassumption.
    + apply (at_type_coherent_l _ _ _ _ _ _ _ HQ HTT); exact HRr.
Qed.

Definition eval_maps ρ M N := forall m, eval_exp M ρ m -> eval_exp N ρ m.

Lemma related_rewrite : forall ρ ρ' A B M M' N N',
    exp_related_at ρ ρ' A M M' ->
    eval_maps ρ A B -> eval_maps ρ' A B ->
    eval_maps ρ M N -> eval_maps ρ' M' N' ->
    exp_related_at ρ ρ' B N N'.
Proof.
  intros ρ ρ' A B M M' N N' (R & (a & a' & Ha & Ha' & HA) & m & m' & Hm & Hm' & HR)
    HL HR' HML HMR.
  exists R; split; [exists a, a' | exists m, m']; repeat split; auto.
Qed.

Lemma kind_rewrite : forall i Γ A B,
    kind_at i Γ A ->
    (forall ρ ρ', env_related Γ ρ ρ' -> eval_maps ρ A B /\ eval_maps ρ' A B) ->
    kind_at i Γ B.
Proof.
  intros i Γ A B H HX ρ ρ' HE.
  destruct (H _ _ HE) as (a & a' & Ha & Ha' & HR).
  destruct (HX _ _ HE) as [HL HR']; exists a, a'; repeat split; auto.
Qed.

Lemma map_eval_identity : forall ρ M, eval_maps ρ M M.
Proof. firstorder. Qed.

Lemma eval_lift : forall σ ρ θ x, eval_sub σ ρ θ ->
    eval_sub (Syntax.q σ) (extend_env ρ x) (extend_env θ x).
Proof.
  intros σ ρ θ x H; apply eval_sub_extend.
  - eapply eval_sub_compose; [apply eval_sub_weaken | exact H].
  - apply eval_exp_var.
Qed.

Lemma eval_sub_under_id : forall ρ M, eval_maps ρ M (a_sub M a_id).
Proof. intros ρ M m H; eapply eval_exp_sub; [apply eval_sub_id | exact H]. Qed.

Lemma eval_flatten_compose : forall ρ M σ τ,
    eval_maps ρ (a_sub M (a_compose σ τ)) (a_sub (a_sub M σ) τ).
Proof.
  intros ρ M σ τ m H; inversion H; subst.
  match goal with H : eval_sub (a_compose _ _) _ _ |- _ => inversion H; subst end.
  eapply eval_exp_sub; [eassumption | eapply eval_exp_sub; eassumption].
Qed.

Lemma eval_univ_sub : forall Γ Δ σ i,
    sub_related Γ Δ σ σ ->
    exp_related Γ (a_typ (S i)) (a_sub (a_typ i) σ) (a_typ i).
Proof.
  intros Γ Δ σ i Hσ ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  eapply related_rewrite; [exact (semantic_universe Γ i _ _ HE) | | | |];
    try apply map_eval_identity.
  intros m Hm; eapply eval_exp_sub; [exact Hθ | inversion Hm; constructor].
Qed.
Lemma eval_nat_sub : forall Γ Δ σ,
    sub_related Γ Δ σ σ ->
    exp_related Γ (a_typ 0) (a_sub a_nat σ) a_nat.
Proof.
  intros Γ Δ σ Hσ ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  eapply related_rewrite; [exact (semantic_natural_type Γ _ _ HE) | | | |];
    try apply map_eval_identity.
  intros m Hm; eapply eval_exp_sub; [exact Hθ | inversion Hm; constructor].
Qed.
Lemma eval_zero_sub : forall Γ Δ σ,
    sub_related Γ Δ σ σ ->
    exp_related Γ a_nat (a_sub a_zero σ) a_zero.
Proof.
  intros Γ Δ σ Hσ ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  eapply related_rewrite; [exact (semantic_zero Γ _ _ HE) | | | |];
    try apply map_eval_identity.
  intros m Hm; eapply eval_exp_sub; [exact Hθ | inversion Hm; constructor].
Qed.
Lemma eval_succ_sub : forall Γ Δ σ M,
    sub_related Γ Δ σ σ -> exp_related Δ a_nat M M ->
    exp_related Γ a_nat (a_sub (a_succ M) σ) (a_succ (a_sub M σ)).
Proof.
  intros Γ Δ σ M Hσ HM ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  destruct (from_nat _ _ _ _ (HM _ _ HD)) as (m & m' & Hm & Hm' & HR).
  apply at_nat; exists (d_succ m), (d_succ m'); split; [|split].
  - eapply eval_exp_sub; [exact Hθ | now apply eval_exp_succ].
  - apply eval_exp_succ; eapply eval_exp_sub; eassumption.
  - now apply nat_rel_succ.
Qed.
Lemma eval_exp_sub_id : forall Γ A M, exp_related Γ A M M ->
    exp_related Γ A (a_sub M a_id) M.
Proof.
  intros Γ A M HM ρ ρ' HE.
  eapply related_rewrite; [exact (HM _ _ HE) | | | |];
    try apply map_eval_identity; apply eval_sub_under_id.
Qed.
Lemma eval_exp_sub_compose : forall Γ Δ Θ σ τ A M,
    sub_related Γ Δ τ τ -> sub_related Δ Θ σ σ -> exp_related Θ A M M ->
    exp_related Γ (a_sub A (a_compose σ τ)) (a_sub M (a_compose σ τ)) (a_sub (a_sub M σ) τ).
Proof.
  intros Γ Δ Θ σ τ A M Hτ Hσ HM ρ ρ' HE.
  pose proof (semantic_compose _ _ _ _ _ _ _ Hτ Hσ) as Hστ.
  eapply related_rewrite; [exact (exp_related_substitution _ _ _ _ _ _ _ Hστ HM _ _ HE) | | | |];
    try apply map_eval_identity; apply eval_flatten_compose.
Qed.

Lemma eval_var_zero_sub : forall Γ Δ σ A M,
    sub_related Γ Δ σ σ -> exp_related Γ (a_sub A σ) M M ->
    exp_related Γ (a_sub A σ) (a_sub (a_var 0) (a_extend σ M)) M.
Proof.
  intros Γ Δ σ A M Hσ HM ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  eapply related_rewrite; [exact (HM _ _ HE) | | | |]; try apply map_eval_identity.
  intros m Hm; eapply eval_exp_sub; [eapply eval_sub_extend; eassumption | apply eval_exp_var].
Qed.
Lemma eval_var_succ_sub : forall Γ Δ σ A M x B,
    sub_related Γ Δ σ σ -> exp_related Γ (a_sub A σ) M M -> ctx_lookup x B Δ ->
    exp_related Γ (a_sub B σ) (a_sub (a_var (S x)) (a_extend σ M)) (a_sub (a_var x) σ).
Proof.
  intros Γ Δ σ A M x B Hσ HM Hlookup ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  destruct (HM _ _ HE) as (_ & _ & m & m' & Hm & Hm' & _).
  pose proof (exp_related_substitution _ _ _ _ _ _ _ Hσ (semantic_var _ _ _ Hlookup) _ _ HE) as HR.
  eapply related_rewrite; [exact HR | | | |]; try apply map_eval_identity.
  intros v Hv; inversion Hv; subst.
  resolve_eval.
  match goal with H : eval_exp (a_var x) θ _ |- _ => inversion H; subst end.
  eapply eval_exp_sub with (ρ' := extend_env θ m); [eapply eval_sub_extend; eassumption | exact (eval_exp_var (S x) (extend_env θ m))].
Qed.
Lemma eval_var_weaken : forall Γ A B x, ctx_lookup x A Γ ->
    exp_related (B :: Γ) (a_sub A a_weaken) (a_sub (a_var x) a_weaken) (a_var (S x)).
Proof.
  intros Γ A B x H ρ ρ' [HE Htail].
  destruct (semantic_var _ _ _ H _ _ HE) as (R & (a & a' & Ha & Ha' & HT) & m & m' & Hm & Hm' & HR).
  inversion Hm'; subst.
  exists R; split.
  - exists a, a'; repeat split; try assumption; (eapply eval_exp_sub; [apply eval_sub_weaken | eassumption]).
  - exists m, (ρ' (S x)); split; [eapply eval_exp_sub; [apply eval_sub_weaken | exact Hm] |].
    split; [exact (eval_exp_var (S x) ρ') | exact HR].
Qed.

Lemma eval_pi_beta : forall Γ i A B M N,
    kind_at i Γ A -> exp_related (A :: Γ) B M M -> exp_related Γ A N N ->
    exp_related Γ (a_sub B (a_extend a_id N)) (a_app (a_fn A M) N) (a_sub M (a_extend a_id N)).
Proof.
  intros Γ i A B M N HA HM HN ρ ρ' HE.
  pose proof (semantic_cons _ _ _ _ _ HA HN) as Hsub.
  eapply related_rewrite; [exact (exp_related_substitution _ _ _ _ _ _ _ Hsub HM _ _ HE) | | | |];
    try apply map_eval_identity.
  intros m Hm; inversion Hm; subst.
  match goal with H : eval_sub (a_extend _ _) _ _ |- _ => inversion H; subst end.
  match goal with H : eval_sub a_id _ _ |- _ => inversion H; subst end.
  eapply eval_exp_app; [apply eval_exp_fn | eassumption | apply eval_app_fn; eassumption].
Qed.

Lemma eval_fst_beta : forall Γ A B M N,
    exp_related Γ A M M -> exp_related Γ (a_sub B (a_extend a_id M)) N N ->
    exp_related Γ A (a_fst (a_pair M A N B)) M.
Proof.
  intros Γ A B M N HM HN ρ ρ' HE.
  destruct (HN _ _ HE) as (_ & _ & n & n' & Hn & Hn' & _).
  eapply related_rewrite; [exact (HM _ _ HE) | | | |]; try apply map_eval_identity.
  intros m Hm; eapply eval_exp_fst; [eapply eval_exp_pair; eassumption | constructor].
Qed.
Lemma eval_snd_beta : forall Γ A B M N,
    exp_related Γ A M M -> exp_related Γ (a_sub B (a_extend a_id M)) N N ->
    exp_related Γ (a_sub B (a_extend a_id M)) (a_snd (a_pair M A N B)) N.
Proof.
  intros Γ A B M N HM HN ρ ρ' HE.
  destruct (HM _ _ HE) as (_ & _ & m & m' & Hm & Hm' & _).
  eapply related_rewrite; [exact (HN _ _ HE) | | | |]; try apply map_eval_identity.
  intros n Hn; eapply eval_exp_snd; [eapply eval_exp_pair; eassumption | constructor].
Qed.

Lemma eval_pi_eta : forall Γ A B M,
    exp_related Γ (a_pi A B) M M ->
    exp_related Γ (a_pi A B) M (a_fn A (a_app (a_sub M a_weaken) (a_var 0))).
Proof.
  intros Γ A B M HM ρ ρ' HE.
  destruct (HM _ _ HE) as (V & (a & a' & Ha & Ha' & [i HT]) & f & f' & Hf & Hf' & HV).
  exists V; split; [exists a, a'; repeat split; try assumption; now exists i |].
  inversion Ha; inversion Ha'; subst; clear Ha Ha'.
  apply model_type_view in HT; cbn in HT; destruct HT as (R & T & HT & HC & HB & HX).
  exists f, (d_fn ρ' (a_app (a_sub M a_weaken) (a_var 0))); split; [exact Hf |].
  split; [apply eval_exp_fn |].
  apply HX; intros x x' Hx.
  destruct (proj2 (HX _ _) HV _ _ Hx) as (v & v' & Hv & Hv' & Hrel).
  exists v, v'; split; [exact Hv |]; split; [|exact Hrel].
  apply eval_app_fn; eapply eval_exp_app.
  - eapply eval_exp_sub; [apply eval_sub_weaken | exact Hf'].
  - apply eval_exp_var.
  - exact Hv'.
Qed.

Lemma eval_sigma_eta : forall Γ A B M,
    exp_related Γ (a_sigma A B) M M ->
    exp_related Γ (a_sigma A B) M (a_pair (a_fst M) A (a_snd M) B).
Proof.
  intros Γ A B M HM ρ ρ' HE.
  destruct (HM _ _ HE) as (V & (a & a' & Ha & Ha' & [i HT]) & p & p' & Hp & Hp' & HV).
  exists V; split; [exists a, a'; repeat split; try assumption; now exists i |].
  inversion Ha; inversion Ha'; subst; clear Ha Ha'.
  apply model_type_view in HT; cbn in HT; destruct HT as (R & T & HT & HC & HB & HX).
  destruct (proj2 (HX _ _) HV) as (x & x' & y & y' & Hx & Hx' & Hy & Hy' & HRx & HRy).
  exists p, (d_pair x' y'); split; [exact Hp |]; split.
  - apply eval_exp_pair; [eapply eval_exp_fst | eapply eval_exp_snd]; eassumption.
  - apply HX; exists x, x', y, y'; repeat split; try assumption; constructor.
Qed.

Lemma semantic_sub_context : forall Γ Δ Δ' σ τ,
    sub_related Γ Δ σ τ -> context_related Δ Δ' -> sub_related Γ Δ' σ τ.
Proof.
  intros Γ Δ Δ' σ τ H HS ρ ρ' HE.
  destruct (H _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  exists θ, θ'; repeat split; auto.
Qed.

Lemma eval_sub_id_law : forall Γ Δ σ, sub_related Γ Δ σ σ ->
    sub_related Γ Δ (a_compose a_id σ) σ /\ sub_related Γ Δ (a_compose σ a_id) σ.
Proof.
  intros Γ Δ σ H; split; intros ρ ρ' HE;
    destruct (H _ _ HE) as (θ & θ' & Hθ & Hθ' & HD);
    exists θ, θ'; repeat split; try assumption.
  - eapply eval_sub_compose; [exact Hθ | constructor].
  - eapply eval_sub_compose; [constructor | exact Hθ].
Qed.
Lemma eval_sub_assoc_law : forall Γ Δ Θ Ψ σ τ υ,
    sub_related Γ Δ υ υ -> sub_related Δ Θ τ τ -> sub_related Θ Ψ σ σ ->
    sub_related Γ Ψ (a_compose (a_compose σ τ) υ) (a_compose σ (a_compose τ υ)).
Proof.
  intros Γ Δ Θ Ψ σ τ υ Hυ Hτ Hσ ρ ρ' HE.
  destruct (Hυ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  destruct (Hτ _ _ HD) as (η & η' & Hη & Hη' & HT).
  destruct (Hσ _ _ HT) as (χ & χ' & Hχ & Hχ' & HP).
  exists χ, χ'; repeat split; try assumption.
  - eapply eval_sub_compose; [exact Hθ | eapply eval_sub_compose; eassumption].
  - eapply eval_sub_compose; [eapply eval_sub_compose; eassumption | exact Hχ'].
Qed.
Lemma eval_sub_extend_compose_law : forall Γ Δ Θ σ τ A M i,
    sub_related Δ Θ σ σ -> kind_at i Θ A -> exp_related Δ (a_sub A σ) M M ->
    sub_related Γ Δ τ τ ->
    sub_related Γ (A :: Θ) (a_compose (a_extend σ M) τ) (a_extend (a_compose σ τ) (a_sub M τ)).
Proof.
  intros Γ Δ Θ σ τ A M i Hσ HA HM Hτ ρ ρ' HE.
  destruct (semantic_compose _ _ _ _ _ _ _ Hτ (semantic_extend _ _ _ _ _ _ _ _ Hσ HA HM) _ _ HE)
    as (θ & θ' & Hθ & Hθ' & HD).
  exists θ, θ'; split; [exact Hθ |]; split; [|exact HD].
  inversion Hθ'; subst.
  match goal with H : eval_sub (a_extend _ _) _ _ |- _ => inversion H; subst end.
  apply eval_sub_extend.
  - eapply eval_sub_compose; eassumption.
  - eapply eval_exp_sub; eassumption.
Qed.
Lemma eval_sub_projection_law : forall Γ Δ σ A M,
    sub_related Γ Δ σ σ -> exp_related Γ (a_sub A σ) M M ->
    sub_related Γ Δ (a_compose a_weaken (a_extend σ M)) σ.
Proof.
  intros Γ Δ σ A M Hσ HM ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  destruct (HM _ _ HE) as (_ & _ & m & m' & Hm & Hm' & _).
  exists θ, θ'; repeat split; try assumption.
  eapply eval_sub_compose; [apply eval_sub_extend; eassumption | exact (eval_sub_weaken (extend_env θ m))].
Qed.
Lemma eval_sub_eta_law : forall Γ Δ σ A,
    sub_related Γ (A :: Δ) σ σ ->
    sub_related Γ (A :: Δ) σ (a_extend (a_compose a_weaken σ) (a_sub (a_var 0) σ)).
Proof.
  intros Γ Δ σ A Hσ ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  exists θ, θ'; split; [exact Hθ |]; split; [|exact HD].
  destruct HD as [Htail (a & a' & R & Ha & Ha' & HR & Hval & Heta & Heta')].
  rewrite Heta'.
  apply eval_sub_extend.
  - eapply eval_sub_compose; [exact Hθ' | apply eval_sub_weaken].
  - eapply eval_exp_sub; [exact Hθ' | apply eval_exp_var].
Qed.

Lemma eval_pi_sub : forall Γ Δ σ i A B,
    sub_related Γ Δ σ σ -> kind_at i Δ A -> kind_at i (A :: Δ) B ->
    exp_related Γ (a_typ i) (a_sub (a_pi A B) σ) (a_pi (a_sub A σ) (a_sub B (Syntax.q σ))).
Proof.
  intros Γ Δ σ i A B Hσ HA HB ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  destruct (prepare_binder i i Δ A A B B _ _ HD HA (HA _ _ HD) HB)
    as (a & a' & R & T & Ha & Ha' & HT & HC & Hcod).
  apply at_universe.
  exists (d_pi a θ B), (d_pi a' ρ' (a_sub B (Syntax.q σ))); repeat split.
  - eapply eval_exp_sub; [exact Hθ | now apply eval_exp_pi].
  - apply eval_exp_pi; eapply eval_exp_sub; eassumption.
  - exists (pi_rel R T). apply model_pi; [exact HT | |].
    + intros x x' Hx; destruct (HC _ _ Hx) as (b & b' & Hb & Hb').
      exists b, b'; split; [exact Hb | eapply eval_exp_sub; [exact (eval_lift _ _ _ _ Hθ') | exact Hb']].
    + intros x x' Hx b b' Hb Hb'.
      inversion Hb'; subst.
      pose proof (eval_lift _ _ _ x' Hθ') as Hlift; resolve_eval.
      eapply Hcod; eassumption.
Qed.
Lemma eval_sigma_sub : forall Γ Δ σ i A B,
    sub_related Γ Δ σ σ -> kind_at i Δ A -> kind_at i (A :: Δ) B ->
    exp_related Γ (a_typ i) (a_sub (a_sigma A B) σ) (a_sigma (a_sub A σ) (a_sub B (Syntax.q σ))).
Proof.
  intros Γ Δ σ i A B Hσ HA HB ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  destruct (prepare_binder i i Δ A A B B _ _ HD HA (HA _ _ HD) HB)
    as (a & a' & R & T & Ha & Ha' & HT & HC & Hcod).
  apply at_universe.
  exists (d_sigma a θ B), (d_sigma a' ρ' (a_sub B (Syntax.q σ))); repeat split.
  - eapply eval_exp_sub; [exact Hθ | now apply eval_exp_sigma].
  - apply eval_exp_sigma; eapply eval_exp_sub; eassumption.
  - exists (sigma_rel R T). apply model_sigma; [exact HT | |].
    + intros x x' Hx; destruct (HC _ _ Hx) as (b & b' & Hb & Hb').
      exists b, b'; split; [exact Hb | eapply eval_exp_sub; [exact (eval_lift _ _ _ _ Hθ') | exact Hb']].
    + intros x x' Hx b b' Hb Hb'.
      inversion Hb'; subst.
      pose proof (eval_lift _ _ _ x' Hθ') as Hlift; resolve_eval.
      eapply Hcod; eassumption.
Qed.
Lemma eval_lambda_sub : forall Γ Δ σ A B M,
    sub_related Γ Δ σ σ -> exp_related Δ (a_pi A B) (a_fn A M) (a_fn A M) ->
    exp_related Γ (a_sub (a_pi A B) σ) (a_sub (a_fn A M) σ)
      (a_fn (a_sub A σ) (a_sub M (Syntax.q σ))).
Proof.
  intros Γ Δ σ A B M Hσ HM ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  destruct (HM _ _ HD) as (V & (p & p' & Hp & Hp' & [i HT]) & f & f' & Hf & Hf' & HV).
  exists V; split.
  - exists p, p'; split; [eapply eval_exp_sub; eassumption |].
    split; [eapply eval_exp_sub; eassumption | now exists i].
  - inversion Hp; inversion Hp'; inversion Hf; inversion Hf'; subst.
    apply model_type_view in HT; cbn in HT; destruct HT as (R & T & HR & HC & Hcod & HX).
    exists (d_fn θ M), (d_fn ρ' (a_sub M (Syntax.q σ))); split.
    + eapply eval_exp_sub; [exact Hθ | apply eval_exp_fn].
    + split; [apply eval_exp_fn |].
      apply HX; intros x x' Hx.
      destruct (proj2 (HX _ _) HV _ _ Hx) as (b & b' & Hb & Hb' & Hrel).
      exists b, b'; split; [exact Hb |]; split; [|exact Hrel].
      inversion Hb'; subst.
      apply eval_app_fn; eapply eval_exp_sub; [exact (eval_lift _ _ _ _ Hθ') | eassumption].
Qed.

Ltac invert_exp_sub :=
  match goal with H : eval_exp (a_sub _ _) _ _ |- _ => inversion H; subst; clear H end.
Ltac invert_sub_extend :=
  match goal with H : eval_sub (a_extend _ _) _ _ |- _ => inversion H; subst; clear H end.
Ltac invert_sub_id :=
  match goal with H : eval_sub a_id _ _ |- _ => inversion H; subst; clear H end.
Ltac invert_inner_eval head :=
  match goal with H : eval_exp head _ _ |- _ => inversion H; subst; clear H end.

Lemma map_app_sub : forall ρ M N σ,
    eval_maps ρ (a_sub (a_app M N) σ) (a_app (a_sub M σ) (a_sub N σ)).
Proof.
  intros ρ M N σ v Hv; invert_exp_sub; invert_inner_eval (a_app M N).
  eapply eval_exp_app; [eapply eval_exp_sub; eassumption | eapply eval_exp_sub; eassumption | eassumption].
Qed.
Lemma map_fst_sub : forall ρ M σ,
    eval_maps ρ (a_sub (a_fst M) σ) (a_fst (a_sub M σ)).
Proof.
  intros ρ M σ v Hv; invert_exp_sub; invert_inner_eval (a_fst M).
  eapply eval_exp_fst; [eapply eval_exp_sub; eassumption | eassumption].
Qed.
Lemma map_snd_sub : forall ρ M σ,
    eval_maps ρ (a_sub (a_snd M) σ) (a_snd (a_sub M σ)).
Proof.
  intros ρ M σ v Hv; invert_exp_sub; invert_inner_eval (a_snd M).
  eapply eval_exp_snd; [eapply eval_exp_sub; eassumption | eassumption].
Qed.
Lemma map_instantiate_sub : forall ρ B N N' σ,
    eval_maps ρ (a_sub N σ) N' ->
    eval_maps ρ (a_sub (a_sub B (a_extend a_id N)) σ) (a_sub B (a_extend σ N')).
Proof.
  intros ρ B N N' σ H m Hm; do 2 invert_exp_sub; invert_sub_extend; invert_sub_id.
  eapply eval_exp_sub; [|eassumption].
  apply eval_sub_extend; [eassumption | apply H; eapply eval_exp_sub; eassumption].
Qed.
Lemma map_pair_sub : forall ρ A B M N σ,
    eval_maps ρ (a_sub (a_pair M A N B) σ)
      (a_pair (a_sub M σ) (a_sub A σ) (a_sub N σ) (a_sub B (Syntax.q σ))).
Proof.
  intros ρ A B M N σ v Hv; invert_exp_sub; invert_inner_eval (a_pair M A N B).
  apply eval_exp_pair; eapply eval_exp_sub; eassumption.
Qed.
Lemma map_eq_sub : forall ρ A M N σ,
    eval_maps ρ (a_sub (a_eq A M N) σ) (a_eq (a_sub A σ) (a_sub M σ) (a_sub N σ)).
Proof.
  intros ρ A M N σ v Hv; invert_exp_sub; invert_inner_eval (a_eq A M N).
  apply eval_exp_eq; eapply eval_exp_sub; eassumption.
Qed.
Lemma map_refl_sub : forall ρ A M σ,
    eval_maps ρ (a_sub (a_refl A M) σ) (a_refl (a_sub A σ) (a_sub M σ)).
Proof.
  intros ρ A M σ v Hv; invert_exp_sub; invert_inner_eval (a_refl A M).
  apply eval_exp_refl; eapply eval_exp_sub; eassumption.
Qed.
Lemma map_typ_sub_inv : forall ρ σ i,
    eval_maps ρ (a_sub (a_typ i) σ) (a_typ i).
Proof. intros ρ σ i v Hv; invert_exp_sub; invert_inner_eval (a_typ i); constructor. Qed.

Lemma eval_app_sub : forall Γ Δ σ A B M N,
    sub_related Γ Δ σ σ -> exp_related Δ (a_pi A B) M M -> exp_related Δ A N N ->
    exp_related Γ (a_sub B (a_extend σ (a_sub N σ)))
      (a_sub (a_app M N) σ) (a_app (a_sub M σ) (a_sub N σ)).
Proof.
  intros Γ Δ σ A B M N Hσ HM HN ρ ρ' HE.
  eapply related_rewrite; [exact (exp_related_substitution _ _ _ _ _ _ _ Hσ
      (semantic_application _ _ _ _ _ _ _ HM HN) _ _ HE) | | | |];
    auto using map_instantiate_sub, map_eval_identity, map_app_sub.
Qed.
Lemma eval_fst_sub : forall Γ Δ σ A B M,
    sub_related Γ Δ σ σ -> exp_related Δ (a_sigma A B) M M ->
    exp_related Γ (a_sub A σ) (a_sub (a_fst M) σ) (a_fst (a_sub M σ)).
Proof.
  intros Γ Δ σ A B M Hσ HM ρ ρ' HE.
  eapply related_rewrite; [exact (exp_related_substitution _ _ _ _ _ _ _ Hσ
      (semantic_fst _ _ _ _ _ HM) _ _ HE) | | | |]; auto using map_eval_identity, map_fst_sub.
Qed.
Lemma eval_snd_sub : forall Γ Δ σ A B M,
    sub_related Γ Δ σ σ -> exp_related Δ (a_sigma A B) M M ->
    exp_related Γ (a_sub B (a_extend σ (a_fst (a_sub M σ))))
      (a_sub (a_snd M) σ) (a_snd (a_sub M σ)).
Proof.
  intros Γ Δ σ A B M Hσ HM ρ ρ' HE.
  eapply related_rewrite; [exact (exp_related_substitution _ _ _ _ _ _ _ Hσ
      (semantic_snd _ _ _ _ _ HM) _ _ HE) | | | |];
    auto using map_instantiate_sub, map_eval_identity, map_fst_sub, map_snd_sub.
Qed.
Lemma eval_pair_substitution : forall Γ Δ σ A B M N,
    sub_related Γ Δ σ σ -> exp_related Δ (a_sigma A B) (a_pair M A N B) (a_pair M A N B) ->
    exp_related Γ (a_sub (a_sigma A B) σ)
      (a_sub (a_pair M A N B) σ) (a_pair (a_sub M σ) (a_sub A σ) (a_sub N σ) (a_sub B (Syntax.q σ))).
Proof.
  intros Γ Δ σ A B M N Hσ HM ρ ρ' HE.
  eapply related_rewrite; [exact (exp_related_substitution _ _ _ _ _ _ _ Hσ HM _ _ HE) | | | |];
    auto using map_eval_identity, map_pair_sub.
Qed.
Lemma eval_eq_substitution : forall Γ Δ σ i A M N,
    sub_related Γ Δ σ σ -> exp_related Δ (a_typ i) (a_eq A M N) (a_eq A M N) ->
    exp_related Γ (a_typ i) (a_sub (a_eq A M N) σ) (a_eq (a_sub A σ) (a_sub M σ) (a_sub N σ)).
Proof.
  intros Γ Δ σ i A M N Hσ HM ρ ρ' HE.
  eapply related_rewrite; [exact (exp_related_substitution _ _ _ _ _ _ _ Hσ HM _ _ HE) | | | |];
    auto using map_eval_identity, map_eq_sub, map_typ_sub_inv.
Qed.
Lemma eval_refl_substitution : forall Γ Δ σ A M,
    sub_related Γ Δ σ σ -> exp_related Δ (a_eq A M M) (a_refl A M) (a_refl A M) ->
    exp_related Γ (a_sub (a_eq A M M) σ) (a_sub (a_refl A M) σ) (a_refl (a_sub A σ) (a_sub M σ)).
Proof.
  intros Γ Δ σ A M Hσ HM ρ ρ' HE.
  eapply related_rewrite; [exact (exp_related_substitution _ _ _ _ _ _ _ Hσ HM _ _ HE) | | | |];
    auto using map_eval_identity, map_refl_sub.
Qed.

Lemma kind_nat_result : forall Γ i A M,
    kind_at i (a_nat :: Γ) A -> exp_related Γ a_nat M M ->
    kind_at i Γ (a_sub A (a_extend a_id M)).
Proof.
  intros; eapply kind_subst; [eapply semantic_cons; [apply kind_nat | eassumption] | eassumption].
Qed.

Lemma eval_nat_beta_zero : forall Γ A Z Suc,
    exp_related Γ (a_sub A (a_extend a_id a_zero)) Z Z ->
    exp_related Γ (a_sub A (a_extend a_id a_zero)) (a_natrec A Z Suc a_zero) Z.
Proof.
  intros Γ A Z Suc HZ ρ ρ' HE.
  eapply related_rewrite; [exact (HZ _ _ HE) | | | |]; try apply map_eval_identity.
  intros m Hm; eapply eval_exp_natrec; [apply eval_exp_zero | apply eval_natrec_zero; exact Hm].
Qed.

Lemma map_nat_motive_step : forall ρ A Z Suc M,
    eval_maps ρ
      (a_sub (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1))))
        (a_extend (a_extend a_id M) (a_natrec A Z Suc M)))
      (a_sub A (a_extend a_id (a_succ M))).
Proof.
  intros ρ A Z Suc M v H; invert_exp_sub; do 2 invert_sub_extend; invert_sub_id.
  invert_exp_sub; invert_sub_extend.
  match goal with H : eval_sub (a_compose a_weaken a_weaken) _ _ |- _ => inversion H; subst; clear H end.
  repeat match goal with H : eval_sub a_weaken _ _ |- _ => inversion H; subst; clear H end.
  match goal with H : eval_exp (a_succ _) _ _ |- _ => inversion H; subst; clear H end.
  match goal with H : eval_exp (a_var _) _ _ |- _ => inversion H; subst; clear H end.
  eapply eval_exp_sub; [apply eval_sub_extend; [constructor | apply eval_exp_succ; eassumption] | eassumption].
Qed.

Lemma eval_nat_beta_succ : forall Γ A Z Suc M i,
    kind_at i (a_nat :: Γ) A ->
    exp_related Γ (a_sub A (a_extend a_id a_zero)) Z Z ->
    exp_related (A :: a_nat :: Γ) (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc Suc ->
    exp_related Γ a_nat M M ->
    exp_related Γ (a_sub A (a_extend a_id (a_succ M))) (a_natrec A Z Suc (a_succ M))
      (a_sub Suc (a_extend (a_extend a_id M) (a_natrec A Z Suc M))).
Proof.
  intros Γ A Z Suc M i HA HZ HS HM ρ ρ' HE.
  pose proof (semantic_natrec _ _ _ _ _ _ _ _ _ _ HA
     (fun θ θ' H => at_universe _ _ _ _ _ (HA θ θ' H)) HZ HS HM) as Hrec.
  pose proof (semantic_cons _ _ _ _ _ (kind_nat Γ) HM) as HMsub.
  pose proof (semantic_extend _ _ _ _ _ _ _ _ HMsub HA Hrec) as Hsub.
  eapply related_rewrite; [exact (exp_related_substitution _ _ _ _ _ _ _ Hsub HS _ _ HE) | | | |];
    try apply map_nat_motive_step; try apply map_eval_identity.
  intros m Hm; invert_exp_sub; do 2 invert_sub_extend; invert_sub_id.
  invert_inner_eval (a_natrec A Z Suc M); resolve_eval.
  eapply eval_exp_natrec; [apply eval_exp_succ; eassumption | eapply eval_natrec_succ; eassumption].
Qed.

Lemma map_equality_branch_beta : forall ρ A B M,
    eval_maps ρ (a_sub (equality_branch_type A B) (a_extend a_id M))
      (equality_result_type B M M (a_refl A M)).
Proof.
  intros ρ A B M v H; unfold equality_branch_type in H.
  invert_exp_sub; invert_sub_extend; invert_sub_id; invert_exp_sub;
  do 2 invert_sub_extend; invert_sub_id.
  repeat match goal with H : eval_exp (a_refl _ _) _ _ |- _ => inversion H; subst; clear H end.
  repeat match goal with H : eval_exp (a_var _) _ _ |- _ => inversion H; subst; clear H end.
  eapply eval_equality_result_type; try eassumption; now apply eval_exp_refl.
Qed.

Lemma eval_equality_beta : forall Γ i A B BR M,
    kind_at i Γ A -> exp_related Γ A M M ->
    exp_related (A :: Γ) (equality_branch_type A B) BR BR ->
    exp_related Γ (equality_result_type B M M (a_refl A M))
      (a_eqrec A B BR M M (a_refl A M)) (a_sub BR (a_extend a_id M)).
Proof.
  intros Γ i A B BR M HA HM HBR ρ ρ' HE.
  pose proof (semantic_cons _ _ _ _ _ HA HM) as HMsub.
  destruct (HA _ _ HE) as (a & a' & Ha & Ha' & R & HT).
  eapply related_rewrite; [exact (exp_related_substitution _ _ _ _ _ _ _ HMsub HBR _ _ HE) | | | |];
    try apply map_equality_branch_beta; try apply map_eval_identity.
  intros r Hr; invert_exp_sub; invert_sub_extend; invert_sub_id.
  eapply eval_exp_eqrec; [exact Ha | eassumption | eassumption | apply eval_exp_refl; eassumption | apply eval_eqrec_refl; eassumption].
Qed.

Lemma eval_natrec_sub : forall Γ Δ σ i A Z Suc M,
    sub_related Γ Δ σ σ ->
    kind_at i (a_nat :: Δ) A ->
    exp_related Δ (a_sub A (a_extend a_id a_zero)) Z Z ->
    exp_related (A :: a_nat :: Δ) (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc Suc ->
    exp_related Δ a_nat M M ->
    exp_related Γ (a_sub A (a_extend σ (a_sub M σ))) (a_sub (a_natrec A Z Suc M) σ)
      (a_natrec (a_sub A (Syntax.q σ)) (a_sub Z σ) (a_sub Suc (Syntax.q (Syntax.q σ))) (a_sub M σ)).
Proof.
  intros Γ Δ σ i A Z Suc M Hσ HA HZ HS HM ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  assert (env_nat : forall x x', nat_rel x x' ->
    env_related (a_nat :: Δ) (extend_env θ x) (extend_env θ' x')).
  { intros; eapply env_related_extend; [exact HD | constructor | constructor | exists 0; apply model_nat | assumption]. }
  destruct (choose_family i nat_rel θ A ρ' (a_sub A (Syntax.q σ))) as (R & HC & Hcod).
  {
    intros x x' Hx; destruct (HA _ _ (env_nat _ _ Hx)) as (b & b' & Hb & Hb' & T & HT).
    exists b, b', T; split; [exact Hb |]. split; [|exact HT].
    eapply eval_exp_sub; [exact (eval_lift _ _ _ _ Hθ') | exact Hb'].
  }
  destruct (HZ _ _ HD) as (ZR & (a0 & a0' & Ha0 & Ha0' & HZR) & z & z' & Hz & Hz' & Hzz).
  assert (Hzs : eval_exp (a_sub Z σ) ρ' z') by (eapply eval_exp_sub; eassumption).
  destruct (HC _ _ nat_rel_zero) as (b0 & b0' & Hb0 & Hb0').
  assert (Hb0s : eval_exp (a_sub A (a_extend a_id a_zero)) θ b0).
  { eapply eval_exp_sub; [apply eval_sub_extend; constructor | exact Hb0]. }
  pose proof (exp_unique _ _ _ Ha0 _ Hb0s) as E; subst a0.
  pose proof (type_values_equiv_l _ _ _ _ _ HZR
    (ex_intro _ i (Hcod _ _ nat_rel_zero _ _ Hb0 Hb0'))) as HX.
  assert (Hstep : forall m m', nat_rel m m' -> forall x x', R m m' x x' ->
    exists y y', eval_exp Suc (extend_env (extend_env θ m) x) y /\
      eval_exp (a_sub Suc (Syntax.q (Syntax.q σ))) (extend_env (extend_env ρ' m') x') y' /\
      R (d_succ m) (d_succ m') y y').
  {
    intros m m' Hm x x' Hx.
    destruct (HA _ _ (env_nat _ _ Hm)) as (a & a' & Ha & Ha' & T & HT).
    destruct (HC _ _ Hm) as (b & b' & Hb & Hb').
    pose proof (exp_unique _ _ _ Hb _ Ha) as E; subst b.
    pose proof (at_type_coherent_l _ _ _ _ _ _ _ (Hcod _ _ Hm _ _ Ha Hb') HT) as Hcast.
    assert (Henv : env_related (A :: a_nat :: Δ)
      (extend_env (extend_env θ m) x) (extend_env (extend_env θ' m') x')).
    { eapply env_related_extend; [exact (env_nat _ _ Hm) | exact Ha | exact Ha' | exists i; exact HT | now apply Hcast]. }
    destruct (HS _ _ Henv) as (SR & (c & c' & Hc & Hc' & HTc) & y & y' & Hy & Hy' & Hyy).
    pose proof (nat_rel_succ _ _ Hm) as Hsm.
    destruct (HC _ _ Hsm) as (d & d' & Hd & Hd').
    assert (Hsim : eval_exp (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1))))
                   (extend_env (extend_env θ m) x) d).
    { eapply eval_exp_sub; [|exact Hd].
      apply eval_sub_extend; [eapply eval_sub_compose; constructor | apply eval_exp_succ, eval_exp_var]. }
    pose proof (exp_unique _ _ _ Hc _ Hsim) as E; subst c.
    pose proof (type_values_equiv_l _ _ _ _ _ HTc (ex_intro _ i (Hcod _ _ Hsm _ _ Hd Hd'))) as Hout.
    exists y, y'; split; [exact Hy |]; split; [|now apply Hout].
    eapply eval_exp_sub; [apply eval_lift, eval_lift; exact Hθ' | exact Hy'].
  }
  destruct (from_nat _ _ _ _ (HM _ _ HD)) as (m & m' & Hm & Hm' & Hmr).
  destruct (nat_model_eliminate i R θ ρ' A (a_sub A (Syntax.q σ)) Z (a_sub Z σ) Suc (a_sub Suc (Syntax.q (Syntax.q σ))) z z' HC Hcod Hz Hzs
    (proj1 (HX _ _) Hzz) Hstep _ _ Hmr) as (v & v' & Hv & Hv' & Hvr).
  destruct (HA _ _ (env_nat _ _ Hmr)) as (a & a' & Ha & Ha' & T & HT).
  destruct (HC _ _ Hmr) as (b & b' & Hb & Hb').
  pose proof (exp_unique _ _ _ Hb _ Ha) as E; subst b.
  pose proof (at_type_coherent_l _ _ _ _ _ _ _ (Hcod _ _ Hmr _ _ Ha Hb') HT) as HR.
  exists T; split.
  - exists a, a'; split; [|split]; try (exists i; exact HT).
    + eapply eval_exp_sub; [apply eval_sub_extend; [exact Hθ | eapply eval_exp_sub; eassumption] | exact Ha].
    + eapply eval_exp_sub; [apply eval_sub_extend; [exact Hθ' | eapply eval_exp_sub; eassumption] | exact Ha'].
  - exists v, v'; split; [|split].
    + eapply eval_exp_sub; [exact Hθ | eapply eval_exp_natrec; eassumption].
    + eapply eval_exp_natrec; [eapply eval_exp_sub; eassumption | exact Hv'].
    + now apply HR.
Qed.

Definition equality_subst_result σ B M N P :=
  a_sub B (a_extend (a_extend (a_extend σ (a_sub M σ)) (a_sub N σ)) (a_sub P σ)).

Lemma eval_equality_subst_result : forall σ ρ θ B M N P x y p b,
    eval_sub σ ρ θ ->
    eval_exp M θ x -> eval_exp N θ y -> eval_exp P θ p ->
    eval_exp B (extend_three θ x y p) b ->
    eval_exp (equality_subst_result σ B M N P) ρ b.
Proof.
  intros; unfold equality_subst_result; eapply eval_exp_sub; [|eassumption].
  do 3 (apply eval_sub_extend; [|eapply eval_exp_sub; eassumption]).
  assumption.
Qed.

Lemma kind_equality_subst_result : forall Γ Δ σ B M N P j,
    sub_related Γ Δ σ σ ->
    kind_at j Δ (equality_result_type B M N P) ->
    kind_at j Γ (equality_subst_result σ B M N P).
Proof.
  intros Γ Δ σ B M N P j Hσ HK.
  eapply kind_rewrite; [exact (kind_subst _ _ _ _ _ Hσ HK) |].
  intros ρ ρ' HE; split; intros b Hb;
    unfold equality_result_type in Hb; do 2 invert_exp_sub; do 3 invert_sub_extend; invert_sub_id;
    eapply eval_equality_subst_result; eassumption.
Qed.

Lemma eval_eqrec_sub : forall Γ Δ σ i j A B BR M N P,
    sub_related Γ Δ σ σ ->
    kind_at i Δ A -> kind_at j (equality_context Δ A) B ->
    exp_related (A :: Δ) (equality_branch_type A B) BR BR ->
    exp_related Δ A M M -> exp_related Δ A N N -> exp_related Δ (a_eq A M N) P P ->
    exp_related Γ (equality_subst_result σ B M N P) (a_sub (a_eqrec A B BR M N P) σ)
      (a_eqrec (a_sub A σ) (a_sub B (Syntax.q (Syntax.q (Syntax.q σ))))
        (a_sub BR (Syntax.q σ)) (a_sub M σ) (a_sub N σ) (a_sub P σ)).
Proof.
  intros Γ Δ σ i j A B BR M N P Hσ HA HB HBR HM HN HP ρ ρ' HE.
  destruct (Hσ _ _ HE) as (θ & θ' & Hθ & Hθ' & HD).
  destruct (HA _ _ HD) as (a & a' & Ha & Ha' & R & HT).
  set (lift_B := a_sub B (Syntax.q (Syntax.q (Syntax.q σ)))).
  assert (Hmot : equality_motives j R θ B ρ' lift_B).
  {
    intros x y p x' y' p' Hx Hy Hp.
    pose proof (relate_equality_context _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD Ha Ha' HT Hx Hy Hp) as HC.
    destruct (HB _ _ HC) as (b & b' & Hb & Hb' & Q & HQ).
    exists b, b', Q; split; [exact Hb |]; split; [|exact HQ].
    unfold lift_B, extend_three; eapply eval_exp_sub; [apply eval_lift, eval_lift, eval_lift; exact Hθ' | exact Hb'].
  }
  assert (Hbr : equality_branches j R θ B BR ρ' lift_B (a_sub BR (Syntax.q σ))).
  {
    intros x x' Hx.
    assert (Henv : env_related (A :: Δ) (extend_env θ x) (extend_env θ' x')).
    { eapply env_related_extend; [exact HD | exact Ha | exact Ha' | exists i; exact HT | exact Hx]. }
    assert (HR : eq_rel R x x x' x' (d_refl x) (d_refl x')) by now apply eq_rel_refl.
    destruct (Hmot _ _ _ _ _ _ Hx Hx HR) as (b & b' & Q & Hb & Hb' & HQ).
    destruct (HBR _ _ Henv) as (V & (c & c' & Hc & Hc' & HV) & r & r' & Hr & Hr' & Hrr).
    pose proof (exp_unique _ _ _ Hc _ (eval_equality_branch_type _ _ _ _ _ Hb)) as E; subst c.
    pose proof (type_values_equiv_l _ _ _ _ _ HV (ex_intro _ j HQ)) as HX.
    exists b, b', Q, r, r'; repeat split; try assumption; [|now apply HX].
    eapply eval_exp_sub; [exact (eval_lift _ _ _ _ Hθ') | exact Hr'].
  }
  destruct (semantic_equality_evaluation _ _ _ _ _ _ _ _ _ _ _ _ _ _ HD Ha Ha' HT HM HN HP)
    as (x & y & p & x' & y' & p' & Hx & Hy & Hp & Hx' & Hy' & Hp' & HRx & HRy & HRp).
  destruct (equality_model_eliminate j i a a' R B lift_B BR (a_sub BR (Syntax.q σ)) θ ρ' HT Hmot Hbr
    _ _ _ _ _ _ HRx HRy HRp) as (b & b' & Q & r & r' & Hb & Hb' & HQ & Hr & Hr' & HRr).
  assert (HBr : eval_exp B (extend_three θ' x' y' p') b').
  {
    unfold lift_B, extend_three in Hb'.
    inversion Hb'; subst.
    pose proof (eval_lift _ _ _ p' (eval_lift _ _ _ y' (eval_lift _ _ _ x' Hθ'))) as Hlift.
    resolve_eval. assumption.
  }
  exists Q; split.
  - exists b, b'; split; [eapply eval_equality_subst_result; eassumption |].
    split; [eapply eval_equality_subst_result; eassumption | exists j; exact HQ].
  - exists r, r'; split; [|split; [|exact HRr]].
    + eapply eval_exp_sub; [exact Hθ | eapply eval_exp_eqrec; eassumption].
    + eapply eval_exp_eqrec; [eapply eval_exp_sub; eassumption | eapply eval_exp_sub; eassumption |
        eapply eval_exp_sub; eassumption | eapply eval_exp_sub; eassumption | exact Hr'].
Qed.

Fixpoint context_bounded (Γ : ctx) : Prop :=
  match Γ with nil => True | A :: Δ => context_bounded Δ /\ kind_bounded Δ A end.
Definition context_valid Γ := env_has_initial Γ /\ context_bounded Γ.

Lemma bounded_kind : forall Γ A i, kind_at i Γ A -> kind_bounded Γ A.
Proof. intros; eexists; eassumption. Qed.

Lemma kind_lookup : forall Γ A x, ctx_lookup x A Γ -> context_bounded Γ -> kind_bounded Γ A.
Proof.
  intros Γ A x H; induction H; intros [HE HA].
  - eapply kind_bounded_subst; [apply semantic_weaken | exact HA].
  - eapply kind_bounded_subst; [apply semantic_weaken | now apply IHctx_lookup].
Qed.

Lemma kind_bounded_pi : forall Γ A B i, kind_at i Γ A ->
    kind_bounded (A :: Γ) B -> kind_bounded Γ (a_pi A B).
Proof.
  intros Γ A B i HA [j HB]. exists (Nat.max i j).
  apply kind_pi.
  - eapply kind_lift; [apply Nat.le_max_l | exact HA].
  - eapply kind_lift; [apply Nat.le_max_r | exact HB].
Qed.

Lemma kind_instance : forall i Γ A B M, kind_at i Γ A ->
    kind_at i (A :: Γ) B -> exp_related Γ A M M ->
    kind_at i Γ (a_sub B (a_extend a_id M)).
Proof. eauto using kind_subst, semantic_cons. Qed.

Lemma kind_instance_subst : forall i Γ Δ A B M M' σ,
    kind_at i Δ A -> kind_at i (A :: Δ) B -> exp_related Δ A M M ->
    sub_related Γ Δ σ σ ->
    (forall ρ, eval_maps ρ (a_sub M σ) M') ->
    kind_at i Γ (a_sub B (a_extend σ M')).
Proof.
  intros i Γ Δ A B M M' σ HA HB HM HS HX.
  eapply kind_rewrite; [exact (kind_subst _ _ _ _ _ HS (kind_instance _ _ _ _ _ HA HB HM)) |].
  intros; split; apply map_instantiate_sub, HX.
Qed.

Lemma kind_nat_subst_result : forall i Γ Δ A M σ,
    kind_at i (a_nat :: Δ) A -> exp_related Δ a_nat M M -> sub_related Γ Δ σ σ ->
    kind_at i Γ (a_sub A (a_extend σ (a_sub M σ))).
Proof. intros i Γ Δ A M σ HA HM HS; exact (kind_instance_subst i Γ Δ a_nat A M (a_sub M σ) σ (kind_lift 0 i _ _ (Nat.le_0_l i) (kind_nat Δ)) HA HM HS (fun ρ => map_eval_identity ρ _)). Qed.

Lemma kind_bounded_convert : forall Γ A i,
    exp_related Γ (a_typ i) A A -> kind_bounded Γ A.
Proof. eauto using kind_from_typing, bounded_kind. Qed.

Lemma context_valid_empty : context_valid nil.
Proof. split; [exists empty_env; split; [constructor | exact I] | exact I]. Qed.
Lemma context_valid_extend : forall Γ A i,
    context_valid Γ -> exp_related Γ (a_typ i) A A -> context_valid (A :: Γ).
Proof.
  intros Γ A i [HI HB] HA.
  split; [eapply semantic_initial_cons; eassumption | simpl; eauto using kind_bounded_convert].
Qed.

Create HintDb mctt_understanding.
#[local] Hint Resolve
  context_valid_empty context_valid_extend kind_bounded_convert
  semantic_context_extend semantic_subtype_convert semantic_subtype_trans semantic_subtype_univ
  semantic_subtype_pi semantic_subtype_sigma
  semantic_sub_context semantic_id semantic_weaken semantic_compose semantic_extend
  sub_related_sym sub_related_trans
  semantic_universe semantic_natural_type semantic_zero semantic_succ semantic_var
  semantic_pi_codes semantic_sigma_codes semantic_lambda semantic_application
  semantic_fst semantic_snd semantic_pair semantic_eq_codes semantic_refl
  semantic_natrec semantic_eqrec exp_related_substitution
  exp_related_sym
  eval_univ_sub eval_nat_sub eval_zero_sub eval_succ_sub eval_exp_sub_id eval_exp_sub_compose
  eval_var_zero_sub eval_var_succ_sub eval_var_weaken
  eval_pi_beta eval_fst_beta eval_snd_beta eval_pi_eta eval_sigma_eta
  eval_sub_assoc_law eval_sub_extend_compose_law eval_sub_projection_law eval_sub_eta_law
  eval_pi_sub eval_sigma_sub eval_lambda_sub eval_app_sub eval_fst_sub eval_snd_sub
  eval_pair_substitution eval_eq_substitution eval_refl_substitution
  eval_nat_beta_zero eval_nat_beta_succ eval_equality_beta eval_natrec_sub eval_eqrec_sub
  kind_from_typing bounded_kind kind_universe kind_nat kind_pi kind_sigma kind_eq
  kind_bounded_pi kind_bounded_subst kind_lookup kind_instance kind_nat_result
  kind_equality_result kind_equality_subst_result kind_nat_subst_result map_eval_identity
  : mctt_understanding.
#[local] Hint Extern 2 (context_related nil nil) => intros; exact I : mctt_understanding.
#[local] Hint Extern 2 (sub_related _ _ (a_compose a_id ?σ) ?σ) =>
  eapply (proj1 (eval_sub_id_law _ _ _ _)); eassumption : mctt_understanding.
#[local] Hint Extern 2 (sub_related _ _ (a_compose ?σ a_id) ?σ) =>
  eapply (proj2 (eval_sub_id_law _ _ _ _)); eassumption : mctt_understanding.

Definition sub_valid Γ Δ σ :=
  sub_related Γ Δ σ σ /\ context_bounded Γ /\ context_bounded Δ.

Lemma fundamental_evaluation :
  (forall Γ, wf_ctx Γ -> context_valid Γ) /\
  (forall Γ Δ, wf_ctx_sub Γ Δ -> context_related Γ Δ) /\
  (forall Γ A M, wf_exp Γ A M -> term_valid Γ A M M) /\
  (forall Γ A M N, wf_exp_eq Γ A M N -> term_valid Γ A M N) /\
  (forall Γ Δ σ, wf_sub Γ Δ σ -> sub_valid Γ Δ σ) /\
  (forall Γ Δ σ τ, wf_sub_eq Γ Δ σ τ -> sub_related Γ Δ σ τ) /\
  (forall Γ A B, wf_subtyp Γ A B -> subtype_related Γ A B).
Proof.
  apply syntactic_wf_mut_ind; intros;
    repeat match goal with
    | H : term_valid _ _ _ _ |- _ => destruct H
    | H : sub_valid _ _ _ |- _ => destruct H as [? [? ?]]
    | H : context_valid _ |- _ =>
        let K := fresh "Hbound" in
        lazymatch type of H with
        | context_valid ?Γ =>
          lazymatch goal with _ : context_bounded Γ |- _ => fail | _ => pose proof (proj2 H) as K end
        end
    | H : kind_bounded _ _ |- _ => destruct H
    | H : exp_related ?Γ (a_typ ?i) ?A ?B |- _ =>
        let K := fresh "Hkind" in
        lazymatch goal with
        | _ : kind_at i Γ A |- _ => fail
        | _ => pose proof (kind_from_typing i Γ A (exp_related_self _ _ _ _ H)) as K
        end
    end;
    try match goal with |- term_valid _ _ _ _ => split end;
    try match goal with |- sub_valid _ _ _ => split; [|split] end.
  all: repeat match goal with
    | H : exp_related ?Γ ?A ?M ?N |- _ =>
      lazymatch goal with
      | _ : exp_related Γ A M M |- _ => fail
      | _ => let K := fresh "Hself" in pose proof (exp_related_self _ _ _ _ H) as K
      end
    end.
  all: try solve [eauto 3 with mctt_understanding].
  all: try solve [eapply exp_related_subtype; eassumption].
  all: try solve [eapply exp_related_trans; eassumption].
  all: try solve [eapply kind_instance_subst; eauto 3 using map_fst_sub with mctt_understanding].
  all: try solve [eapply kind_bounded_subst; [eapply sub_related_self_l; eassumption | eauto 3 with mctt_understanding]].
  all: try solve [eapply bounded_kind; eapply kind_instance_subst; eauto 3 using map_fst_sub with mctt_understanding].
  all: try solve [solve [simpl in *; tauto]].
  all: try solve [eapply bounded_kind; eauto 5 with mctt_understanding].
  all: try solve [eapply kind_bounded_subst; [apply semantic_weaken | eapply kind_lookup; [eassumption | simpl in *; tauto]]].
  all: try solve [cbn [context_bounded]; split; eauto 3 with mctt_understanding].
  all: try solve [unfold context_related; intros; exact I].
  - eapply bounded_kind; eapply kind_subst; [eapply semantic_compose; eassumption | eassumption].
  - match goal with
    | HL : exp_related ?Γ ?A ?M ?N, HR : exp_related ?Γ ?A ?N ?P |- exp_related ?Γ ?A ?M ?P =>
      exact (exp_related_trans _ _ _ _ _ HL HR)
    end.
  Unshelve. all: assumption.
Qed.

Lemma typing_contexts :
  (forall Γ, wf_ctx Γ -> True) /\
  (forall Γ A M, wf_exp Γ A M -> wf_ctx Γ) /\
  (forall Γ Δ σ, wf_sub Γ Δ σ -> wf_ctx Γ /\ wf_ctx Δ).
Proof.
  apply syntactic_wf_mut_ind'; intros;
    try match goal with H : wf_ctx (_ :: _) |- _ => inversion H end;
    intuition eauto using wf_ctx_extend.
Qed.

Lemma normalization_exists : forall Γ A M,
    wf_exp Γ A M -> exists W, nbe Γ M A W.
Proof.
  intros Γ A M H.
  destruct fundamental_evaluation as (Hctx & _ & Hexp & _).
  pose proof (proj1 (proj2 typing_contexts) _ _ _ H) as HG.
  destruct (proj1 (Hctx _ HG)) as (ρ & Hinit & Henv).
  destruct (proj1 (Hexp _ _ _ H) _ _ Henv)
    as (R & (a & a' & Ha & Ha' & [i HK]) & m & m' & Hm & Hm' & HV).
  pose proof (exp_unique _ _ _ Ha' _ Ha) as E; subst a'.
  pose proof (exp_unique _ _ _ Hm' _ Hm) as E; subst m'.
  exact (nbe_from_model _ _ _ _ _ _ _ _ Hinit Ha Hm HK HV).
Qed.
Lemma conversion_respects_nbe : forall Γ A M N,
    wf_ctx Γ -> wf_exp_eq Γ A M N ->
    exists W, nbe Γ M A W /\ nbe Γ N A W.
Proof.
  intros Γ A M N HG HE.
  destruct fundamental_evaluation as (Hctx & _ & _ & Hexp & _).
  destruct (proj1 (Hctx _ HG)) as (ρ & Hinit & Henv).
  destruct (proj1 (Hexp _ _ _ _ HE) _ _ Henv)
    as (R & (a & a' & Ha & Ha' & [i HK]) & m & n & Hm & Hn & HV).
  pose proof (exp_unique _ _ _ Ha' _ Ha) as E; subst a'.
  destruct (model_readback _ (universes_valid i) _ _ _ HK) as [_ [HQ _]].
  destruct (HQ _ _ HV (length Γ)) as (W & HW & HW').
  exists W; split; eapply nbe_run; eassumption.
Qed.

End SoundnessSupport.


Module SyntacticSoundness.

Import SoundnessSupport.

(* Typed quotation connects semantic readback with the McTT equality rules. *)

Lemma expression_context : forall Γ A M, wf_exp Γ A M -> wf_ctx Γ.
Proof. exact (proj1 (proj2 typing_contexts)). Qed.

Lemma substitution_contexts : forall Γ Δ σ, wf_sub Γ Δ σ -> wf_ctx Γ /\ wf_ctx Δ.
Proof. exact (proj2 (proj2 typing_contexts)). Qed.

Lemma reflexive_expression : forall Γ A M, wf_exp Γ A M -> wf_exp_eq Γ A M M.
Proof.
  intros Γ A M H.
  eapply wf_exp_eq_trans; [apply wf_exp_eq_sym |]; now apply wf_exp_eq_sub_id.
Qed.

Lemma reflexive_substitution : forall Γ Δ σ, wf_sub Γ Δ σ -> wf_sub_eq Γ Δ σ σ.
Proof.
  intros Γ Δ σ H.
  eapply wf_sub_eq_trans; [apply wf_sub_eq_sym |]; now apply wf_sub_eq_id_compose_right.
Qed.

Lemma convert_expression : forall Γ A B i M,
    wf_exp Γ A M -> wf_exp Γ (a_typ i) B -> wf_exp_eq Γ (a_typ i) A B ->
    wf_exp Γ B M.
Proof. eauto using wf_exp_subtyp, wf_subtyp_refl. Qed.

Lemma convert_equality : forall Γ A B i M N,
    wf_exp_eq Γ A M N -> wf_exp Γ (a_typ i) B -> wf_exp_eq Γ (a_typ i) A B ->
    wf_exp_eq Γ B M N.
Proof. eauto using wf_exp_eq_subtyp, wf_subtyp_refl. Qed.

Lemma cumulative_type : forall Γ A i j,
    wf_exp Γ (a_typ i) A -> i <= j -> wf_exp Γ (a_typ j) A.
Proof.
  intros Γ A i j H Hj. destruct Hj.
  - exact H.
  - pose proof (expression_context _ _ _ H) as HG.
    eapply wf_exp_subtyp; [exact H | now apply wf_typ | apply wf_subtyp_univ; [exact HG | lia]].
Qed.

Lemma cumulative_type_equality : forall Γ A B i j,
    wf_ctx Γ -> wf_exp_eq Γ (a_typ i) A B -> i <= j ->
    wf_exp_eq Γ (a_typ j) A B.
Proof.
  intros Γ A B i j HG H Hj. destruct Hj.
  - exact H.
  - eapply wf_exp_eq_subtyp; [exact H | now apply wf_typ | apply wf_subtyp_univ; [exact HG | lia]].
Qed.

Lemma substitute_type : forall Γ Δ σ A i,
    wf_sub Γ Δ σ -> wf_exp Δ (a_typ i) A -> wf_exp Γ (a_typ i) (a_sub A σ).
Proof.
  intros Γ Δ σ A i HS HA.
  pose proof (proj1 (substitution_contexts _ _ _ HS)) as HΓ.
  eapply convert_expression; eauto using wf_exp_sub, wf_typ, wf_exp_eq_typ_sub.
Qed.

Lemma substitute_type_equality : forall Γ Δ σ τ A B i,
    wf_sub Γ Δ σ -> wf_sub_eq Γ Δ σ τ -> wf_exp_eq Δ (a_typ i) A B ->
    wf_exp_eq Γ (a_typ i) (a_sub A σ) (a_sub B τ).
Proof.
  intros Γ Δ σ τ A B i HS HE HAB.
  pose proof (proj1 (substitution_contexts _ _ _ HS)) as HΓ.
  eapply convert_equality; eauto using wf_exp_eq_sub_cong, wf_typ, wf_exp_eq_typ_sub.
Qed.

Lemma weaken_type : forall Γ A B i,
    wf_ctx (B :: Γ) -> wf_exp Γ (a_typ i) A -> wf_exp (B :: Γ) (a_typ i) (a_sub A a_weaken).
Proof. eauto using substitute_type, wf_sub_weaken. Qed.

Lemma variable_type : forall Γ x A,
    wf_ctx Γ -> ctx_lookup x A Γ -> exists i, wf_exp Γ (a_typ i) A.
Proof.
  intros Γ x A HΓ HL; induction HL; inversion HΓ; subst.
  - eauto using substitute_type, wf_sub_weaken.
  - edestruct IHHL as [j Hj]; eauto using substitute_type, wf_sub_weaken.
Qed.

Lemma type_substitution_identity : forall Γ A i,
    wf_exp Γ (a_typ i) A -> wf_exp_eq Γ (a_typ i) (a_sub A a_id) A.
Proof. intros; now apply wf_exp_eq_sub_id. Qed.

Lemma type_substitution_compose : forall Γ Δ Θ σ τ A i,
    wf_sub Γ Δ τ -> wf_sub Δ Θ σ -> wf_exp Θ (a_typ i) A ->
    wf_exp_eq Γ (a_typ i) (a_sub A (a_compose σ τ)) (a_sub (a_sub A σ) τ).
Proof.
  intros Γ Δ Θ σ τ A i HT HS HA.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HC.
  pose proof (proj1 (substitution_contexts _ _ _ HT)) as HΓ.
  eapply convert_equality; eauto using wf_exp_eq_sub_compose, wf_typ, wf_exp_eq_typ_sub.
Qed.

Lemma substitute_weakening : forall Γ Δ σ A B M i j,
    wf_sub Γ Δ σ ->
    wf_exp Δ (a_typ i) A ->
    wf_exp Δ (a_typ j) B ->
    wf_exp Γ (a_sub A σ) M ->
    wf_exp_eq Γ (a_typ j)
      (a_sub (a_sub B a_weaken) (a_extend σ M)) (a_sub B σ).
Proof.
  intros Γ Δ σ A B M i j HS HA HB HM.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HM) as HE.
  pose proof (wf_sub_weaken _ _ (proj2 (substitution_contexts _ _ _ HE))) as HW.
  eapply wf_exp_eq_trans.
  - apply wf_exp_eq_sym; eapply type_substitution_compose; eassumption.
  - eapply substitute_type_equality.
    + eapply wf_sub_compose; eassumption.
    + exact (wf_sub_eq_p_extend _ _ _ _ _ _ HS HA HM).
    + now apply reflexive_expression.
Qed.

Lemma substitute_two_weakenings : forall Γ Δ σ A B M N i j,
    wf_sub Γ Δ σ ->
    wf_exp Δ (a_typ i) A ->
    wf_exp Δ (a_typ j) B ->
    wf_exp Γ (a_sub A σ) M ->
    wf_exp Γ (a_sub (a_sub A a_weaken) (a_extend σ M)) N ->
    wf_exp_eq Γ (a_typ j)
      (a_sub (a_sub B (a_compose a_weaken a_weaken)) (a_extend (a_extend σ M) N)) (a_sub B σ).
Proof.
  intros Γ Δ σ A B M N i j HS HA HB HM HN.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HM) as HE.
  pose proof (proj2 (substitution_contexts _ _ _ HE)) as HD.
  pose proof (weaken_type _ _ _ _ HD HA) as HAW.
  pose proof (wf_sub_extend _ _ _ _ _ _ HE HAW HN) as HEE.
  pose proof (proj2 (substitution_contexts _ _ _ HEE)) as HDD.
  pose proof (wf_sub_weaken _ _ HD) as HW.
  pose proof (wf_sub_weaken _ _ HDD) as HWW.
  eapply wf_exp_eq_trans.
  - eapply substitute_type_equality; [exact HEE | now apply reflexive_substitution |].
    eapply type_substitution_compose; eassumption.
  - eapply wf_exp_eq_trans.
    + eapply substitute_weakening; eauto using weaken_type.
    + exact (substitute_weakening _ _ _ _ _ _ _ _ HS HA HB HM).
Qed.

Lemma type_of_first_variable : forall Γ A,
    wf_ctx (A :: Γ) -> wf_exp (A :: Γ) (a_sub A a_weaken) (a_var 0).
Proof. eauto using wf_vlookup, here. Qed.

Lemma instantiate_type : forall Γ A M i, wf_exp Γ (a_typ i) A -> wf_exp Γ A M ->
    wf_sub Γ (A :: Γ) (a_extend a_id M).
Proof.
  intros Γ A M i HA HM.
  pose proof (wf_sub_id _ (expression_context _ _ _ HA)) as HI.
  eapply wf_sub_extend; [exact HI | exact HA |].
  eapply convert_expression; eauto using substitute_type, wf_exp_eq_sym, type_substitution_identity.
Qed.

Lemma instantiate_type_congruence : forall Γ A M N i,
    wf_exp Γ (a_typ i) A -> wf_exp_eq Γ A M N ->
    wf_sub_eq Γ (A :: Γ) (a_extend a_id M) (a_extend a_id N).
Proof.
  intros Γ A M N i HA HM.
  pose proof (expression_context _ _ _ HA) as HG.
  pose proof (wf_sub_id _ HG) as HI.
  eapply wf_sub_eq_extend_cong; [now apply wf_sub_eq_id | exact HA |].
  eapply convert_equality; eauto using substitute_type, wf_exp_eq_sym, type_substitution_identity.
Qed.

Lemma lift_substitution : forall Γ Δ σ A i,
    wf_sub Γ Δ σ -> wf_exp Δ (a_typ i) A ->
    wf_sub (a_sub A σ :: Γ) (A :: Δ) (Syntax.q σ).
Proof.
  intros Γ Δ σ A i HS HA.
  pose proof (proj1 (substitution_contexts _ _ _ HS)) as HΓ.
  pose proof (wf_ctx_extend Γ i _ HΓ (substitute_type _ _ _ _ _ HS HA)) as HG.
  pose proof (wf_sub_weaken _ _ HG) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HW HS) as HSW.
  eapply wf_sub_extend; [exact HSW | exact HA |].
  eapply convert_expression; [now apply type_of_first_variable | eapply substitute_type; eassumption |].
  apply wf_exp_eq_sym; eapply type_substitution_compose; eassumption.
Qed.

Lemma lift_substitution_congruence : forall Γ Δ A σ τ i,
    wf_sub Γ Δ σ -> wf_sub_eq Γ Δ σ τ -> wf_exp Δ (a_typ i) A ->
    wf_sub_eq (a_sub A σ :: Γ) (A :: Δ) (Syntax.q σ) (Syntax.q τ).
Proof.
  intros Γ Δ A σ τ i HS HE HA.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HT.
  pose proof (expression_context _ _ _ HT) as HΓ.
  pose proof (wf_ctx_extend _ _ _ HΓ HT) as HG.
  pose proof (wf_sub_weaken _ _ HG) as HW.
  eapply wf_sub_eq_extend_cong.
  - eapply wf_sub_eq_compose_cong; [now apply wf_sub_eq_weaken | exact HE].
  - exact HA.
  - eapply convert_equality.
    + apply wf_exp_eq_var; [exact HG | apply here].
    + eapply substitute_type; [eapply wf_sub_compose; eassumption | exact HA].
    + apply wf_exp_eq_sym; eapply type_substitution_compose; eassumption.
Qed.

Lemma identity_context_inclusion : forall Γ, wf_ctx Γ -> wf_ctx_sub Γ Γ.
Proof.
  intros Γ H; induction H; eauto using wf_ctx_sub_empty, wf_ctx_sub_extend, wf_subtyp_refl, reflexive_expression.
Qed.

Lemma convert_binder : forall Γ A B i,
    wf_exp Γ (a_typ i) A ->
    wf_exp Γ (a_typ i) B ->
    wf_exp_eq Γ (a_typ i) A B ->
    wf_sub (A :: Γ) (B :: Γ) a_id.
Proof.
  intros Γ A B i HA HB HE.
  pose proof (expression_context _ _ _ HA) as HG.
  eapply wf_sub_subtyp.
  - apply wf_sub_id; eauto using wf_ctx_extend.
  - eauto using wf_ctx_extend.
  - eauto using wf_ctx_sub_extend, identity_context_inclusion, wf_subtyp_refl.
Qed.

Lemma equality_instantiation_types : forall Γ A M1 M2 i,
    wf_exp Γ (a_typ i) A ->
    wf_exp Γ A M1 ->
    wf_exp Γ A M2 ->
    let E := a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0) in
    wf_exp (A :: Γ) (a_typ i) (a_sub A a_weaken) /\
    wf_exp (a_sub A a_weaken :: A :: Γ) (a_typ i) E /\
    wf_exp_eq Γ (a_typ i) (a_sub (a_sub A a_weaken) (a_extend a_id M1)) A /\
    wf_exp_eq Γ (a_typ i) (a_sub E (a_extend (a_extend a_id M1) M2)) (a_eq A M1 M2).
Proof.
  intros Γ A M1 M2 i HA HM1 HM2; cbn zeta.
  pose proof (expression_context _ _ _ HA) as HG.
  pose proof (wf_sub_id _ HG) as HI.
  pose proof (instantiate_type _ _ _ _ HA HM1) as HS.
  pose proof (wf_ctx_extend _ _ _ HG HA) as HGA.
  pose proof (weaken_type _ _ _ _ HGA HA) as HAW.
  pose proof (wf_ctx_extend _ _ _ HGA HAW) as HGAA.
  pose proof (substitute_type _ _ _ _ _ HI HA) as HAI.
  pose proof (wf_exp_eq_sub_id _ _ _ HA) as HAI_A.
  pose proof (convert_expression _ _ _ _ _ HM1 HAI (wf_exp_eq_sym _ _ _ _ HAI_A)) as HM1I.
  pose proof (substitute_type _ _ _ _ _ HS HAW) as HAWS.
  pose proof (substitute_weakening _ _ _ _ _ _ _ _ HI HA HA HM1I) as HAWS_AI.
  assert (HAWS_A : wf_exp_eq Γ (a_typ i) (a_sub (a_sub A a_weaken) (a_extend a_id M1)) A).
  { eapply wf_exp_eq_trans; eassumption. }
  pose proof (convert_expression _ _ _ _ _ HM2 HAWS (wf_exp_eq_sym _ _ _ _ HAWS_A)) as HM2S.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HAW HM2S) as HSS.
  pose proof (wf_sub_weaken _ _ HGAA) as HWW.
  pose proof (wf_sub_weaken _ _ HGA) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HWW HW) as HWWW.
  pose proof (substitute_type _ _ _ _ _ HWWW HA) as HAWW.
  assert (Hx : wf_exp (a_sub A a_weaken :: A :: Γ) (a_sub A (a_compose a_weaken a_weaken)) (a_var 1)).
  {
    eapply convert_expression; [eapply wf_vlookup; [exact HGAA | apply there, here] | exact HAWW |].
    apply wf_exp_eq_sym; eapply type_substitution_compose; eassumption.
  }
  assert (Hy : wf_exp (a_sub A a_weaken :: A :: Γ) (a_sub A (a_compose a_weaken a_weaken)) (a_var 0)).
  {
    eapply convert_expression; [apply type_of_first_variable; exact HGAA | exact HAWW |].
    apply wf_exp_eq_sym; eapply type_substitution_compose; eassumption.
  }
  pose proof (wf_eq _ _ _ _ _ HAWW Hx Hy) as HEq.
  split; [exact HAW |]. split; [exact HEq |]. split; [exact HAWS_A |].
  pose proof (substitute_two_weakenings _ _ _ _ _ _ _ _ _ HI HA HA HM1I HM2S) as HC.
  assert (HCA : wf_exp_eq Γ (a_typ i)
    (a_sub (a_sub A (a_compose a_weaken a_weaken)) (a_extend (a_extend a_id M1) M2)) A).
  { eapply wf_exp_eq_trans; eassumption. }
  assert (H0 : wf_exp_eq Γ A (a_sub (a_var 0) (a_extend (a_extend a_id M1) M2)) M2).
  { eapply convert_equality; [eapply wf_exp_eq_var_0_sub; eassumption | exact HA | exact HAWS_A]. }
  assert (H1 : wf_exp_eq Γ A (a_sub (a_var 1) (a_extend (a_extend a_id M1) M2)) M1).
  {
    eapply convert_equality; [| exact HA | exact HAWS_A].
    eapply wf_exp_eq_trans; [eapply wf_exp_eq_var_S_sub; try eassumption; apply here |].
    eapply convert_equality;
      [exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ HI HA HM1I) | exact HAWS | apply wf_exp_eq_sym; exact HAWS_AI].
  }
  eapply wf_exp_eq_trans; [eapply wf_exp_eq_eq_sub; eassumption |].
  eapply wf_exp_eq_eq_cong; [exact HCA | |].
  - eapply convert_equality; [exact H1 | eapply substitute_type; eassumption | now apply wf_exp_eq_sym].
  - eapply convert_equality; [exact H0 | eapply substitute_type; eassumption | now apply wf_exp_eq_sym].
Qed.

Lemma equality_motive_substitution : forall Γ A M1 M2 N i,
    wf_exp Γ (a_typ i) A ->
    wf_exp Γ A M1 ->
    wf_exp Γ A M2 ->
    wf_exp Γ (a_eq A M1 M2) N ->
    wf_sub Γ (equality_context Γ A)
      (a_extend (a_extend (a_extend a_id M1) M2) N).
Proof.
  intros Γ A M1 M2 N i HA HM1 HM2 HN.
  destruct (equality_instantiation_types _ _ _ _ _ HA HM1 HM2) as (HAW & HEq & HAe & HEqe).
  pose proof (instantiate_type _ _ _ _ HA HM1) as HS.
  pose proof (substitute_type _ _ _ _ _ HS HAW) as HAW'.
  pose proof (convert_expression _ _ _ _ _ HM2 HAW' (wf_exp_eq_sym _ _ _ _ HAe)) as HM2'.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HAW HM2') as HSS.
  pose proof (substitute_type _ _ _ _ _ HSS HEq) as HEq'.
  unfold equality_context.
  eapply wf_sub_extend; [exact HSS | exact HEq |].
  exact (convert_expression _ _ _ _ _ HN HEq' (wf_exp_eq_sym _ _ _ _ HEqe)).
Qed.

Lemma expression_type : forall Γ A M, wf_exp Γ A M -> exists i, wf_exp Γ (a_typ i) A.
Proof.
  intros Γ A M H; induction H.
  - eauto using wf_typ.
  - eauto using wf_typ.
  - eauto using wf_nat.
  - exact IHwf_exp.
  - exists i. eapply substitute_type; [| eassumption].
    eapply instantiate_type; [apply wf_nat; eauto using expression_context | assumption].
  - eauto using wf_typ, expression_context.
  - destruct IHwf_exp2 as [j Hj].
    exists (Nat.max i j).
    eapply wf_pi; eapply cumulative_type; try eassumption; lia.
  - eauto using substitute_type, instantiate_type.
  - eauto using wf_typ, expression_context.
  - eauto using wf_sigma.
  - eauto.
  - eauto using substitute_type, instantiate_type, wf_fst.
  - eauto using variable_type.
  - eauto using wf_typ, expression_context.
  - eauto using wf_eq.
  - eauto using substitute_type, equality_motive_substitution.
  - destruct IHwf_exp as [i Hi]. exists i. eauto using substitute_type.
  - eauto.
Qed.

Lemma weakening_extension_fusion : forall Γ Δ Θ σ τ A M i,
    wf_sub Γ Δ τ ->
    wf_sub Δ Θ σ ->
    wf_exp Θ (a_typ i) A ->
    wf_exp Δ (a_sub A σ) M ->
    wf_sub_eq Γ Θ
      (a_compose a_weaken (a_compose (a_extend σ M) τ))
      (a_compose σ τ).
Proof.
  intros Γ Δ Θ σ τ A M i HT HS HA HM.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HM) as HE.
  pose proof (wf_sub_weaken _ _ (proj2 (substitution_contexts _ _ _ HE))) as HW.
  eapply wf_sub_eq_trans.
  - apply wf_sub_eq_sym. eapply wf_sub_eq_compose_assoc; eassumption.
  - eapply wf_sub_eq_compose_cong.
    + exact (reflexive_substitution _ _ _ HT).
    + eapply wf_sub_eq_p_extend; eassumption.
Qed.

Lemma substitute_into_lift : forall Γ Δ σ A B X i j,
    wf_sub Γ Δ σ ->
    wf_exp Δ (a_typ i) A ->
    wf_exp (A :: Δ) (a_typ j) B ->
    wf_exp Γ (a_sub A σ) X ->
    wf_exp_eq Γ (a_typ j)
      (a_sub (a_sub B (Syntax.q σ)) (a_extend a_id X))
      (a_sub B (a_extend σ X)).
Proof.
  intros Γ Δ σ A B X i j HS HA HB HX.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (instantiate_type _ _ _ _ HAs HX) as HE.
  pose proof (lift_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (proj2 (substitution_contexts _ _ _ HE)) as HG.
  pose proof (wf_sub_weaken _ _ HG) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HW HS) as HSW.
  pose proof (wf_sub_compose _ _ _ _ _ HE HSW) as HSWX.
  assert (H0 : wf_exp (a_sub A σ :: Γ) (a_sub A (a_compose σ a_weaken)) (a_var 0)).
  {
    eapply convert_expression.
    - now apply type_of_first_variable.
    - eapply substitute_type; eassumption.
    - apply wf_exp_eq_sym; eapply type_substitution_compose; eassumption.
  }
  pose proof (wf_sub_id _ (expression_context _ _ _ HX)) as HI.
  assert (HXi : wf_exp Γ (a_sub (a_sub A σ) a_id) X).
  { eapply convert_expression; [exact HX | eapply substitute_type; eassumption |].
    apply wf_exp_eq_sym; now apply type_substitution_identity. }
  assert (Hproj : wf_sub_eq Γ Γ (a_compose a_weaken (a_extend a_id X)) a_id).
  { eapply wf_sub_eq_p_extend; eassumption. }
  assert (Htail : wf_sub_eq Γ Δ
    (a_compose (a_compose σ a_weaken) (a_extend a_id X)) σ).
  {
    eapply wf_sub_eq_trans; [eapply wf_sub_eq_compose_assoc; eassumption |].
    eapply wf_sub_eq_trans; [eapply wf_sub_eq_compose_cong; [exact Hproj | now apply reflexive_substitution] |].
    now apply wf_sub_eq_id_compose_left.
  }
  assert (HXeq : wf_exp_eq Γ (a_sub A (a_compose (a_compose σ a_weaken) (a_extend a_id X)))
                          (a_sub (a_var 0) (a_extend a_id X)) X).
  {
    eapply convert_equality; [exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ HI HAs HXi) | |].
    - eapply substitute_type; eassumption.
    - apply wf_exp_eq_sym. eapply wf_exp_eq_trans.
      + eapply substitute_type_equality; [exact HSWX | exact Htail | now apply reflexive_expression].
      + apply wf_exp_eq_sym; now apply type_substitution_identity.
  }
  assert (HQX : wf_sub_eq Γ (A :: Δ) (a_compose (Syntax.q σ) (a_extend a_id X)) (a_extend σ X)).
  {
    eapply wf_sub_eq_trans.
    - unfold Syntax.q; exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ HSW HA H0 HE).
    - eapply wf_sub_eq_extend_cong; eassumption.
  }
  eapply wf_exp_eq_trans.
  - apply wf_exp_eq_sym; eapply type_substitution_compose; eassumption.
  - eapply substitute_type_equality.
    + eapply wf_sub_compose; eassumption.
    + exact HQX.
    + now apply reflexive_expression.
Qed.

Definition quoted_type Γ i A a :=
  exists W, read_typ (length Γ) a W /\ wf_exp_eq Γ (a_typ i) A W.
Definition quoted_term Γ A M a m :=
  exists W, read_nf (length Γ) (d_dom a m) W /\ wf_exp_eq Γ A M W.
Definition quoted_neutral Γ A M n :=
  exists W, read_ne (length Γ) n W /\ wf_exp_eq Γ A M W.

Lemma quote_type_conversion : forall Γ i A B a,
    wf_exp_eq Γ (a_typ i) A B -> quoted_type Γ i B a -> quoted_type Γ i A a.
Proof.
  intros Γ i A B a E (W & HR & H).
  exists W; split; [exact HR | eapply wf_exp_eq_trans; eassumption].
Qed.
Lemma quote_term_conversion : forall Γ A M N a m,
    wf_exp_eq Γ A M N -> quoted_term Γ A N a m -> quoted_term Γ A M a m.
Proof.
  intros Γ A M N a m E (W & HR & H).
  exists W; split; [exact HR | eapply wf_exp_eq_trans; eassumption].
Qed.
Lemma quote_neutral_conversion : forall Γ A M N n,
    wf_exp_eq Γ A M N -> quoted_neutral Γ A N n -> quoted_neutral Γ A M n.
Proof.
  intros Γ A M N n E (W & HR & H).
  exists W; split; [exact HR | eapply wf_exp_eq_trans; eassumption].
Qed.
Lemma quote_term_type_conversion : forall Γ i A B M a m,
    wf_exp Γ (a_typ i) B -> wf_exp_eq Γ (a_typ i) A B ->
    quoted_term Γ A M a m -> quoted_term Γ B M a m.
Proof.
  intros Γ i A B M a m HB HE (W & HR & HQ).
  exists W; split; [exact HR | eapply convert_equality; eassumption].
Qed.
Lemma quote_type_semantic_conversion : forall Γ i A a b j R,
    at_type j a b R -> quoted_type Γ i A a -> quoted_type Γ i A b.
Proof.
  intros Γ i A a b j R HT (W & HWA & HE).
  destruct (model_readback _ (universes_valid j) _ _ _ HT) as [HQ _].
  destruct (HQ (length Γ)) as (W' & HWA' & HWB).
  pose proof (proj2 (proj2 readback_unique) _ _ _ HWA _ HWA') as <-.
  now exists W.
Qed.
Lemma quote_term_semantic_conversion : forall Γ A M a b m n j R,
    at_type j a b R -> R m n -> quoted_term Γ A M a m -> quoted_term Γ A M b n.
Proof.
  intros Γ A M a b m n j R HT Hmn (W & HWA & HE).
  destruct (model_readback _ (universes_valid j) _ _ _ HT) as [_ [HQ _]].
  destruct (HQ _ _ Hmn (length Γ)) as (W' & HWA' & HWB).
  pose proof (proj1 readback_unique _ _ _ HWA _ HWA') as <-.
  now exists W.
Qed.

Lemma quote_type_nat : forall Γ, wf_ctx Γ -> quoted_type Γ 0 a_nat d_nat.
Proof.
  intros Γ HG; exists nf_nat; split; [constructor | apply reflexive_expression, wf_nat, HG].
Qed.
Lemma quote_type_universe : forall Γ i, wf_ctx Γ ->
    quoted_type Γ (S i) (a_typ i) (d_univ i).
Proof.
  intros Γ i HG; exists (nf_typ i); split; [constructor | apply reflexive_expression, wf_typ, HG].
Qed.
Lemma quote_term_universe : forall Γ i A a,
    quoted_type Γ i A a -> quoted_term Γ (a_typ i) A (d_univ i) a.
Proof.
  intros Γ i A a (W & HR & H); exists W; split; [now constructor | exact H].
Qed.
Lemma quote_term_zero : forall Γ, wf_ctx Γ -> quoted_term Γ a_nat a_zero d_nat d_zero.
Proof.
  intros Γ HG; exists nf_zero; split; [constructor | apply reflexive_expression, wf_zero, HG].
Qed.
Lemma quote_term_succ : forall Γ M m, quoted_term Γ a_nat M d_nat m ->
    quoted_term Γ a_nat (a_succ M) d_nat (d_succ m).
Proof.
  intros Γ M m (W & HR & H); exists (nf_succ W); split; now constructor.
Qed.
Lemma quote_term_natural_neutral : forall Γ M a n,
    quoted_neutral Γ a_nat M n -> quoted_term Γ a_nat M d_nat (d_neut a n).
Proof.
  intros Γ M a n (W & HR & H); exists (nf_neut W); split; [now constructor | exact H].
Qed.
Lemma quote_type_neutral : forall Γ i A a n,
    quoted_neutral Γ (a_typ i) A n -> quoted_type Γ i A (d_neut a n).
Proof.
  intros Γ i A a n (W & HR & H); exists (nf_neut W); split; [now constructor | exact H].
Qed.
Lemma quote_term_opaque : forall Γ A M a n b r,
    quoted_neutral Γ A M r -> quoted_term Γ A M (d_neut a n) (d_neut b r).
Proof.
  intros Γ A M a n b r (W & HR & H); exists (nf_neut W); split; [now constructor | exact H].
Qed.
Lemma quote_term_equality_neutral : forall Γ A M a x y b r,
    quoted_neutral Γ A M r -> quoted_term Γ A M (d_eq a x y) (d_neut b r).
Proof.
  intros Γ A M a x y b r (W & HR & H); exists (nf_neut W); split; [now constructor | exact H].
Qed.

Lemma quote_type_pi : forall Γ i A B a ρ C b,
    wf_exp Γ (a_typ i) A -> quoted_type Γ i A a ->
    eval_exp C (extend_env ρ (d_neut a (d_var (length Γ)))) b ->
    quoted_type (A :: Γ) i B b ->
    quoted_type Γ i (a_pi A B) (d_pi a ρ C).
Proof.
  intros Γ i A B a ρ C b HA (An & HR & HE) Hb (Bn & HBR & HBE).
  exists (nf_pi An Bn); split.
  - eapply read_typ_pi; eassumption.
  - cbn; eapply wf_exp_eq_pi_cong; eassumption.
Qed.
Lemma quote_type_sigma : forall Γ i A B a ρ C b,
    wf_exp Γ (a_typ i) A -> quoted_type Γ i A a ->
    eval_exp C (extend_env ρ (d_neut a (d_var (length Γ)))) b ->
    quoted_type (A :: Γ) i B b ->
    quoted_type Γ i (a_sigma A B) (d_sigma a ρ C).
Proof.
  intros Γ i A B a ρ C b HA (An & HR & HE) Hb (Bn & HBR & HBE).
  exists (nf_sigma An Bn); split.
  - eapply read_typ_sigma; eassumption.
  - cbn; eapply wf_exp_eq_sigma_cong; eassumption.
Qed.
Lemma quote_type_equality : forall Γ i A X Y a x y,
    quoted_type Γ i A a ->
    quoted_term Γ A X a x ->
    quoted_term Γ A Y a y ->
    quoted_type Γ i (a_eq A X Y) (d_eq a x y).
Proof.
  intros Γ i A X Y a x y (A' & HAr & HAe) (X' & HXr & HXe) (Y' & HYr & HYe).
  exists (nf_eq A' X' Y'); split.
  - eapply read_typ_eq; eassumption.
  - cbn; eapply wf_exp_eq_eq_cong; eassumption.
Qed.

Lemma quote_term_pi : forall Γ i A B M a ρ C b m y,
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    wf_exp Γ (a_pi A B) M ->
    quoted_type Γ i A a ->
    eval_app m (d_neut a (d_var (length Γ))) y ->
    eval_exp C (extend_env ρ (d_neut a (d_var (length Γ)))) b ->
    quoted_term (A :: Γ) B (a_app (a_sub M a_weaken) (a_var 0)) b y ->
    quoted_term Γ (a_pi A B) M (d_pi a ρ C) m.
Proof.
  intros Γ i A B M a ρ C b m y HA HB HM (An & HAR & HAE) Happ Hcod (N & HR & HE).
  exists (nf_fn An N); split.
  - eapply read_nf_fn; eassumption.
  - cbn; eapply wf_exp_eq_trans.
    + eapply wf_exp_eq_pi_eta; eassumption.
    + eapply wf_exp_eq_fn_cong; eassumption.
Qed.

Lemma quote_term_sigma : forall Γ i A B M a ρ C b1 b2 m x y,
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    wf_exp Γ (a_sigma A B) M ->
    quoted_type Γ i A a ->
    eval_exp C (extend_env ρ (d_neut a (d_var (length Γ)))) b1 ->
    quoted_type (A :: Γ) i B b1 ->
    eval_fst m x -> eval_snd m y -> eval_exp C (extend_env ρ x) b2 ->
    quoted_term Γ A (a_fst M) a x ->
    quoted_term Γ (a_sub B (a_extend a_id (a_fst M))) (a_snd M) b2 y ->
    quoted_term Γ (a_sigma A B) M (d_sigma a ρ C) m.
Proof.
  intros Γ i A B M a ρ C b1 b2 m x y HA HB HM (An & HAr & HAe) HE1 (Bn & HBr & HBe)
    Hx Hy HE2 (X & HXr & HXe) (Y & HYr & HYe).
  exists (nf_pair X An Y Bn); split.
  - eapply read_nf_sigma; eassumption.
  - cbn; eapply wf_exp_eq_trans.
    + eapply wf_exp_eq_sigma_eta; eassumption.
    + eapply wf_exp_eq_pair_cong; eassumption.
Qed.

Lemma quote_term_refl : forall Γ i A M X Y P a x y m,
    wf_exp Γ (a_typ i) A ->
    wf_exp Γ A X -> wf_exp Γ A Y ->
    wf_exp_eq Γ A M X -> wf_exp_eq Γ A M Y ->
    wf_exp_eq Γ (a_eq A X Y) P (a_refl A M) ->
    quoted_type Γ i A a ->
    quoted_term Γ A M a m ->
    quoted_term Γ (a_eq A X Y) P (d_eq a x y) (d_refl m).
Proof.
  intros Γ i A M X Y P a x y m HA HX HY HMX HMY HP (An & HAr & HAe) (Mn & HMr & HMe).
  exists (nf_refl An Mn); split.
  - eapply read_nf_refl; eassumption.
  - cbn; eapply wf_exp_eq_trans; [exact HP |].
    eapply convert_equality.
    + eapply wf_exp_eq_refl_cong; eassumption.
    + eapply wf_eq; eassumption.
    + eapply wf_exp_eq_eq_cong; [now apply reflexive_expression | exact HMX | exact HMY].
Qed.

Lemma quote_neutral_application : forall Γ i A B M N a m n,
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    quoted_neutral Γ (a_pi A B) M m ->
    quoted_term Γ A N a n ->
    quoted_neutral Γ (a_sub B (a_extend a_id N)) (a_app M N) (d_app m (d_dom a n)).
Proof.
  intros Γ i A B M N a m n HA HB (Nm & HRm & HEm) (Nn & HRn & HEn).
  exists (ne_app Nm Nn); split; [now apply read_ne_app | cbn; eapply wf_exp_eq_app_cong; eassumption].
Qed.
Lemma quote_neutral_fst : forall Γ i A B M n,
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    quoted_neutral Γ (a_sigma A B) M n ->
    quoted_neutral Γ A (a_fst M) (d_fst n).
Proof.
  intros Γ i A B M n HA HB (N & HR & HE).
  exists (ne_fst N); split; [now apply read_ne_fst | cbn; eapply wf_exp_eq_fst_cong; eassumption].
Qed.
Lemma quote_neutral_snd : forall Γ i A B M n,
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    quoted_neutral Γ (a_sigma A B) M n ->
    quoted_neutral Γ (a_sub B (a_extend a_id (a_fst M))) (a_snd M) (d_snd n).
Proof.
  intros Γ i A B M n HA HB (N & HR & HE).
  exists (ne_snd N); split; [now apply read_ne_snd | cbn; eapply wf_exp_eq_snd_cong; eassumption].
Qed.

Lemma quote_neutral_natrec : forall Γ i A Z Suc M ρ C z MS n b b0 bs m,
    wf_exp (a_nat :: Γ) (a_typ i) A ->
    eval_exp C (extend_env ρ (d_neut d_nat (d_var (length Γ)))) b ->
    quoted_type (a_nat :: Γ) i A b ->
    eval_exp C (extend_env ρ d_zero) b0 ->
    quoted_term Γ (a_sub A (a_extend a_id a_zero)) Z b0 z ->
    eval_exp C (extend_env ρ (d_succ (d_neut d_nat (d_var (length Γ))))) bs ->
    eval_exp MS (extend_env (extend_env ρ (d_neut d_nat (d_var (length Γ))))
                         (d_neut b (d_var (S (length Γ))))) m ->
    quoted_term (A :: a_nat :: Γ) (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc bs m ->
    quoted_neutral Γ a_nat M n ->
    quoted_neutral Γ (a_sub A (a_extend a_id M)) (a_natrec A Z Suc M) (d_natrec ρ C z MS n).
Proof.
  intros Γ i A Z Suc M ρ C z MS n b b0 bs m HA Hb (A' & HAr & HAe) Hb0
    (Z' & HZr & HZe) Hbs Hm (S' & HSr & HSe) (M' & HMr & HMe).
  exists (ne_natrec A' Z' S' M'); split.
  - eapply read_ne_natrec; eassumption.
  - cbn; eapply wf_exp_eq_natrec_cong; eassumption.
Qed.

Lemma quote_neutral_eqrec : forall Γ i j A B BR M N P ρ C Cr a x y n b b0 br,
    wf_exp Γ (a_typ i) A -> wf_exp Γ A M -> wf_exp Γ A N ->
    quoted_type Γ i A a ->
    quoted_term Γ A M a x -> quoted_term Γ A N a y ->
    (let u := d_neut a (d_var (length Γ)) in
     let v := d_neut a (d_var (S (length Γ))) in
     eval_exp C (extend_three ρ u v (d_neut (d_eq a u v) (d_var (S (S (length Γ)))))) b) ->
    quoted_type (equality_context Γ A) j B b ->
    (let u := d_neut a (d_var (length Γ)) in
     eval_exp C (extend_three ρ u u (d_refl u)) b0) ->
    eval_exp Cr (extend_env ρ (d_neut a (d_var (length Γ)))) br ->
    quoted_term (A :: Γ) (equality_branch_type A B) BR b0 br ->
    quoted_neutral Γ (a_eq A M N) P n ->
    quoted_neutral Γ (equality_result_type B M N P) (a_eqrec A B BR M N P)
      (d_eqrec ρ a C Cr x y n).
Proof.
  intros Γ i j A B BR M N P ρ C Cr a x y n b b0 br HA HM HN
    (An & HAr & HAe) (Mn & HMr & HMe) (Nn & HNr & HNe) Hb (Bn & HBr & HBe)
    Hb0 Hbr (BRn & HBRr & HBRe) (Pn & HPr & HPe).
  exists (ne_eqrec An Bn BRn Mn Nn Pn); split.
  - cbn [extend_three] in Hb, Hb0; eapply read_ne_eqrec; eassumption.
  - cbn; eapply wf_exp_eq_eqrec_cong; eassumption.
Qed.

Inductive weakening : ctx -> ctx -> sub -> Prop :=
| weakening_identity : forall Γ, wf_ctx Γ -> weakening Γ Γ a_id
| weakening_drop : forall Γ A, wf_ctx (A :: Γ) -> weakening (A :: Γ) Γ a_weaken
| weakening_compose : forall Γ Δ Θ σ τ,
    weakening Γ Δ τ -> weakening Δ Θ σ -> weakening Γ Θ (a_compose σ τ).

Lemma weakening_is_typed : forall Γ Δ σ, weakening Γ Δ σ -> wf_sub Γ Δ σ.
Proof. intros Γ Δ σ H; induction H; eauto using wf_sub_id, wf_sub_weaken, wf_sub_compose. Qed.

Lemma weakening_length : forall Γ Δ σ, weakening Γ Δ σ -> length Δ <= length Γ.
Proof. intros Γ Δ σ H; induction H; simpl; lia. Qed.

Lemma lookup_length : forall Γ x A, ctx_lookup x A Γ -> x < length Γ.
Proof. intros Γ x A H; induction H; simpl; lia. Qed.

Lemma weakening_lookup : forall Γ Δ σ x A i,
    weakening Γ Δ σ ->
    ctx_lookup x A Δ ->
    wf_exp Δ (a_typ i) A ->
    exists B, ctx_lookup (length Γ - length Δ + x) B Γ /\
      wf_exp Γ (a_typ i) B /\
      wf_exp_eq Γ (a_typ i) (a_sub A σ) B /\
      wf_exp_eq Γ B (a_sub (a_var x) σ) (a_var (length Γ - length Δ + x)).
Proof.
  intros Γ Δ σ x A i HS; revert x A i.
  induction HS as [Γ HG|Γ C HG|Γ Δ Θ σ τ HT IHτ HS IHσ]; intros x A i HL HA.
  - rewrite Nat.sub_diag; simpl.
    exists A; repeat split; try assumption.
    + now apply type_substitution_identity.
    + apply wf_exp_eq_sub_id; now apply wf_vlookup.
  - assert (E : length (C :: Γ) - length Γ + x = S x) by (change (S (length Γ) - length Γ + x = S x); lia).
    rewrite E.
    exists (a_sub A a_weaken); repeat split.
    + now apply there.
    + now apply weaken_type.
    + apply reflexive_expression; now apply weaken_type.
    + now apply wf_exp_eq_var_weaken.
  - destruct (IHσ _ _ _ HL HA) as (B & HLB & HB & HEAB & HEvar).
    destruct (IHτ _ _ _ HLB HB) as (C & HLC & HC & HEBC & HEvar').
    pose proof (weakening_is_typed _ _ _ HT) as Hτ.
    pose proof (weakening_is_typed _ _ _ HS) as Hσ.
    assert (E : length Γ - length Θ + x = length Γ - length Δ + (length Δ - length Θ + x)).
    { pose proof (weakening_length _ _ _ HT); pose proof (weakening_length _ _ _ HS); lia. }
    rewrite E.
    exists C; repeat split; try assumption.
    + eapply wf_exp_eq_trans.
      * eapply type_substitution_compose; eassumption.
      * eapply wf_exp_eq_trans; [eapply substitute_type_equality | exact HEBC].
        -- exact Hτ.
        -- now apply reflexive_substitution.
        -- exact HEAB.
    + eapply wf_exp_eq_trans.
      * eapply convert_equality; [eapply wf_exp_eq_sub_compose; try eassumption |exact HC|].
        -- apply wf_vlookup; [exact (proj2 (substitution_contexts _ _ _ Hσ)) | exact HL].
        -- eapply wf_exp_eq_trans.
           ++ eapply type_substitution_compose; eassumption.
           ++ eapply wf_exp_eq_trans; [eapply substitute_type_equality | exact HEBC].
              ** exact Hτ.
              ** now apply reflexive_substitution.
              ** exact HEAB.
      * eapply wf_exp_eq_trans; [| exact HEvar'].
        eapply convert_equality; [eapply wf_exp_eq_sub_cong | exact HC | exact HEBC].
        -- exact HEvar.
        -- now apply reflexive_substitution.
Qed.

Definition neutral_under_weakening Γ A M n :=
  forall Δ σ, weakening Δ Γ σ -> quoted_neutral Δ (a_sub A σ) (a_sub M σ) n.

Lemma variable_neutral_under_weakening : forall Γ x A,
    wf_ctx Γ -> ctx_lookup x A Γ ->
    neutral_under_weakening Γ A (a_var x) (d_var (length Γ - x - 1)).
Proof.
  intros Γ x A HG HL Δ σ Hσ.
  destruct (variable_type _ _ _ HG HL) as [i HA].
  destruct (weakening_lookup _ _ _ _ _ _ Hσ HL HA) as (B & HLB & HB & HE & HM).
  pose proof (lookup_length _ _ _ HL) as Hx.
  pose proof (weakening_length _ _ _ Hσ) as Hlen.
  assert (E : length Δ - (length Γ - x - 1) - 1 = length Δ - length Γ + x) by lia.
  exists (ne_var (length Δ - length Γ + x)); split.
  - rewrite <- E; apply read_ne_var.
  - cbn; eapply convert_equality; [exact HM | | apply wf_exp_eq_sym; exact HE].
    exact (substitute_type _ _ _ _ _ (weakening_is_typed _ _ _ Hσ) HA).
Qed.

Lemma observe_neutral : forall Γ A M n,
    wf_exp Γ A M -> neutral_under_weakening Γ A M n -> quoted_neutral Γ A M n.
Proof.
  intros Γ A M n HM HN.
  pose proof (expression_context _ _ _ HM) as HG.
  destruct (expression_type _ _ _ HM) as (i & HA).
  destruct (HN _ _ (weakening_identity _ HG)) as (N & HNr & HNe).
  exists N; split; [exact HNr |].
  eapply wf_exp_eq_trans.
  - apply wf_exp_eq_sym; now apply wf_exp_eq_sub_id.
  - eapply convert_equality; [exact HNe | exact HA | now apply type_substitution_identity].
Qed.

Lemma weaken_neutral : forall Γ Δ τ A M n,
    weakening Δ Γ τ -> wf_exp Γ A M ->
    neutral_under_weakening Γ A M n ->
    neutral_under_weakening Δ (a_sub A τ) (a_sub M τ) n.
Proof.
  intros Γ Δ τ A M n Hτ HM HN Θ σ Hσ.
  destruct (HN _ _ (weakening_compose _ _ _ _ _ Hσ Hτ)) as (N & HNr & HNe).
  pose proof (weakening_is_typed _ _ _ Hσ) as HS.
  pose proof (weakening_is_typed _ _ _ Hτ) as HT.
  destruct (expression_type _ _ _ HM) as (i & HA).
  exists N; split; [exact HNr |].
  eapply convert_equality.
  - eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; eapply wf_exp_eq_sub_compose; eassumption | exact HNe].
  - eapply substitute_type; [exact HS | eapply substitute_type; eassumption].
  - eapply type_substitution_compose; eassumption.
Qed.

Lemma initial_variable_value : forall Γ ρ x A,
    initial_env Γ ρ -> ctx_lookup x A Γ ->
    exists a, eval_exp A ρ a /\ ρ x = d_neut a (d_var (length Γ - x - 1)).
Proof.
  intros Γ ρ x A HE HL; revert ρ HE; induction HL; intros ρ HE.
  - inversion HE; subst.
    eexists; split.
    + eapply eval_exp_sub; [apply eval_sub_weaken | eassumption].
    + simpl; now rewrite Nat.sub_0_r.
  - inversion HE; subst.
    edestruct IHHL as (b & Ha & E); [eassumption |].
    exists b; split.
    + eapply eval_exp_sub; [apply eval_sub_weaken | exact Ha].
    + exact E.
Qed.

Lemma quote_neutral_type_conversion : forall Γ i A B M n,
    wf_exp Γ (a_typ i) B -> wf_exp_eq Γ (a_typ i) A B ->
    quoted_neutral Γ A M n -> quoted_neutral Γ B M n.
Proof.
  intros Γ i A B M n HB HE (W & HR & HQ).
  exists W; split; [exact HR | eapply convert_equality; eassumption].
Qed.

Lemma convert_neutral_under_weakening : forall Γ i A B M n,
    wf_exp Γ (a_typ i) B -> wf_exp_eq Γ (a_typ i) A B ->
    neutral_under_weakening Γ A M n -> neutral_under_weakening Γ B M n.
Proof.
  intros Γ i A B M n HB HE HN Δ σ HW.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  eapply quote_neutral_type_conversion.
  - exact (substitute_type _ _ _ _ _ HS HB).
  - eapply substitute_type_equality; [exact HS | now apply reflexive_substitution | exact HE].
  - now apply HN.
Qed.

Lemma neutral_under_weakening_conversion : forall Γ A M N n,
    wf_exp_eq Γ A M N ->
    neutral_under_weakening Γ A N n -> neutral_under_weakening Γ A M n.
Proof.
  intros Γ A M N n HE HN Δ σ HW.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  eapply quote_neutral_conversion; [eapply wf_exp_eq_sub_cong; [exact HE | now apply reflexive_substitution] | now apply HN].
Qed.

Lemma substitute_instantiated_type : forall Γ Δ σ A B X i j,
    wf_sub Γ Δ σ ->
    wf_exp Δ (a_typ i) A ->
    wf_exp (A :: Δ) (a_typ j) B ->
    wf_exp Δ A X ->
    wf_exp_eq Γ (a_typ j)
      (a_sub (a_sub B (a_extend a_id X)) σ)
      (a_sub B (a_extend σ (a_sub X σ))).
Proof.
  intros Γ Δ σ A B X i j HS HA HB HX.
  pose proof (wf_sub_id _ (expression_context _ _ _ HA)) as HI.
  pose proof (substitute_type _ _ _ _ _ HI HA) as HAi.
  assert (HXi : wf_exp Δ (a_sub A a_id) X).
  { eapply convert_expression; [exact HX | exact HAi | apply wf_exp_eq_sym; now apply type_substitution_identity]. }
  pose proof (wf_sub_extend _ _ _ _ _ _ HI HA HXi) as HE.
  pose proof (wf_sub_compose _ _ _ _ _ HS HE) as HC.
  pose proof (wf_sub_compose _ _ _ _ _ HS HI) as HIC.
  pose proof (wf_exp_sub _ _ _ _ _ HS HXi) as HXX.
  pose proof (wf_exp_sub _ _ _ _ _ HS HX) as HXs.
  assert (HExt : wf_sub_eq Γ (A :: Δ)
      (a_compose (a_extend a_id X) σ) (a_extend σ (a_sub X σ))).
  {
    eapply wf_sub_eq_trans.
    - exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ HI HA HXi HS).
    - eapply wf_sub_eq_extend_cong.
      + now apply wf_sub_eq_id_compose_right.
      + exact HA.
      + apply reflexive_expression.
        eapply convert_expression; [exact HXX | exact (substitute_type _ _ _ _ _ HIC HA) |].
        apply wf_exp_eq_sym; eapply type_substitution_compose; eassumption.
  }
  eapply wf_exp_eq_trans.
  - apply wf_exp_eq_sym; eapply type_substitution_compose; eassumption.
  - eapply substitute_type_equality; [exact HC | exact HExt | now apply reflexive_expression].
Qed.

Lemma typed_application_after_substitution : forall Γ Δ σ A B M N i j,
    wf_sub Γ Δ σ ->
    wf_exp Δ (a_typ i) A ->
    wf_exp (A :: Δ) (a_typ j) B ->
    wf_exp Δ (a_pi A B) M ->
    wf_exp Γ (a_sub A σ) N ->
    wf_exp Γ (a_sub B (a_extend σ N)) (a_app (a_sub M σ) N).
Proof.
  intros Γ Δ σ A B M N i j HS HA HB HM HN.
  pose proof (cumulative_type _ _ _ _ HA (Nat.le_max_l i j)) as HA'.
  pose proof (cumulative_type _ _ _ _ HB (Nat.le_max_r i j)) as HB'.
  pose proof (lift_substitution _ _ _ _ _ HS HA') as HQ.
  pose proof (substitute_type _ _ _ _ _ HS HA') as HAs.
  pose proof (substitute_type _ _ _ _ _ HQ HB') as HBs.
  assert (HMs : wf_exp Γ (a_pi (a_sub A σ) (a_sub B (Syntax.q σ))) (a_sub M σ)).
  {
    eapply convert_expression.
    - exact (wf_exp_sub _ _ _ _ _ HS HM).
    - eapply wf_pi; eassumption.
    - eapply wf_exp_eq_pi_sub; eassumption.
  }
  eapply convert_expression.
  - eapply wf_app; eassumption.
  - eapply substitute_type; [exact (wf_sub_extend _ _ _ _ _ _ HS HA HN) | exact HB].
  - exact (substitute_into_lift _ _ _ _ _ _ _ _ HS HA HB HN).
Qed.

Lemma neutral_application_under_weakening : forall Γ i A B M N a n m,
    wf_exp Γ (a_typ i) A ->
    wf_exp (A :: Γ) (a_typ i) B ->
    wf_exp Γ (a_pi A B) M ->
    wf_exp Γ A N ->
    neutral_under_weakening Γ (a_pi A B) M m ->
    (forall Δ σ, weakening Δ Γ σ -> quoted_term Δ (a_sub A σ) (a_sub N σ) a n) ->
    neutral_under_weakening Γ (a_sub B (a_extend a_id N)) (a_app M N) (d_app m (d_dom a n)).
Proof.
  intros Γ i A B M N a n m HA HB HM HN Hne HQ Δ σ HW.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  pose proof (lift_substitution _ _ _ _ _ HS HA) as HQS.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (substitute_type _ _ _ _ _ HQS HB) as HBs.
  pose proof (wf_exp_sub _ _ _ _ _ HS HN) as HNs.
  pose proof (instantiate_type _ _ _ _ HA HN) as HI.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HNs) as Htest.
  pose proof (substitute_type _ _ _ _ _ Htest HB) as HtestB.
  pose proof (substitute_type _ _ _ _ _ HS (substitute_type _ _ _ _ _ HI HB)) as Hfinal.
  assert (Hhead : quoted_neutral Δ (a_pi (a_sub A σ) (a_sub B (Syntax.q σ))) (a_sub M σ) m).
  {
    eapply quote_neutral_type_conversion; [eapply wf_pi; eassumption | eapply wf_exp_eq_pi_sub; eassumption |].
    now apply Hne.
  }
  pose proof (quote_neutral_application _ _ _ _ _ _ _ _ _ HAs HBs Hhead (HQ _ _ HW)) as Happ.
  assert (Hnext : quoted_neutral Δ (a_sub B (a_extend σ (a_sub N σ)))
      (a_app (a_sub M σ) (a_sub N σ)) (d_app m (d_dom a n))).
  {
    eapply quote_neutral_type_conversion.
    - exact HtestB.
    - exact (substitute_into_lift _ _ _ _ _ _ _ _ HS HA HB HNs).
    - exact Happ.
  }
  eapply quote_neutral_type_conversion.
  - exact Hfinal.
  - apply wf_exp_eq_sym; exact (substitute_instantiated_type _ _ _ _ _ _ _ _ HS HA HB HN).
  - eapply quote_neutral_conversion; [eapply wf_exp_eq_app_sub; eassumption | exact Hnext].
Qed.

Definition term_under_weakening Γ A M a m :=
  forall Δ σ, weakening Δ Γ σ -> quoted_term Δ (a_sub A σ) (a_sub M σ) a m.

Definition type_under_weakening Γ i A a :=
  forall Δ σ, weakening Δ Γ σ -> quoted_type Δ i (a_sub A σ) a.

Lemma observe_term : forall Γ A M a m, wf_exp Γ A M ->
    term_under_weakening Γ A M a m -> quoted_term Γ A M a m.
Proof.
  intros Γ A M a m HM HQ.
  destruct (expression_type _ _ _ HM) as (i & HA).
  destruct (HQ _ _ (weakening_identity _ (expression_context _ _ _ HM))) as (W & HR & HE).
  exists W; split; [exact HR |].
  eapply wf_exp_eq_trans.
  - apply wf_exp_eq_sym; now apply wf_exp_eq_sub_id.
  - eapply convert_equality; [exact HE | exact HA | now apply type_substitution_identity].
Qed.

Lemma observe_type : forall Γ i A a, wf_exp Γ (a_typ i) A ->
    type_under_weakening Γ i A a -> quoted_type Γ i A a.
Proof.
  intros Γ i A a HA HQ.
  destruct (HQ _ _ (weakening_identity _ (expression_context _ _ _ HA))) as (W & HR & HE).
  exists W; split; [exact HR |].
  eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; now apply wf_exp_eq_sub_id | exact HE].
Qed.

Lemma weaken_term_quote : forall Γ Δ τ A M a m,
    weakening Δ Γ τ -> wf_exp Γ A M ->
    term_under_weakening Γ A M a m ->
    term_under_weakening Δ (a_sub A τ) (a_sub M τ) a m.
Proof.
  intros Γ Δ τ A M a m Hτ HM HQ Θ σ Hσ.
  destruct (HQ _ _ (weakening_compose _ _ _ _ _ Hσ Hτ)) as (W & HR & HE).
  pose proof (weakening_is_typed _ _ _ Hσ) as HS.
  pose proof (weakening_is_typed _ _ _ Hτ) as HT.
  destruct (expression_type _ _ _ HM) as (i & HA).
  exists W; split; [exact HR |].
  eapply convert_equality.
  - eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; eapply wf_exp_eq_sub_compose; eassumption | exact HE].
  - eapply substitute_type; [exact HS | eapply substitute_type; eassumption].
  - eapply type_substitution_compose; eassumption.
Qed.

Lemma convert_term_under_weakening : forall Γ i A B M a m,
    wf_exp Γ (a_typ i) B -> wf_exp_eq Γ (a_typ i) A B ->
    term_under_weakening Γ A M a m -> term_under_weakening Γ B M a m.
Proof.
  intros Γ i A B M a m HB HE HQ Δ σ HW.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  eapply quote_term_type_conversion.
  - exact (substitute_type _ _ _ _ _ HS HB).
  - eapply substitute_type_equality; [exact HS | now apply reflexive_substitution | exact HE].
  - now apply HQ.
Qed.

Lemma term_under_weakening_conversion : forall Γ A M N a m,
    wf_exp_eq Γ A M N -> term_under_weakening Γ A N a m -> term_under_weakening Γ A M a m.
Proof.
  intros Γ A M N a m HE HQ Δ σ HW.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  eapply quote_term_conversion; [eapply wf_exp_eq_sub_cong; [exact HE | now apply reflexive_substitution] | now apply HQ].
Qed.

Lemma neutral_fst_under_weakening : forall Γ i A B M n,
    wf_exp Γ (a_typ i) A ->
    wf_exp (A :: Γ) (a_typ i) B ->
    wf_exp Γ (a_sigma A B) M ->
    neutral_under_weakening Γ (a_sigma A B) M n ->
    neutral_under_weakening Γ A (a_fst M) (d_fst n).
Proof.
  intros Γ i A B M n HA HB HM Hne Δ σ HW.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  pose proof (lift_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (substitute_type _ _ _ _ _ HQ HB) as HBs.
  eapply quote_neutral_conversion; [eapply wf_exp_eq_fst_sub; eassumption |].
  eapply quote_neutral_fst; [exact HAs | exact HBs |].
  eapply quote_neutral_type_conversion.
  - eapply wf_sigma; eassumption.
  - eapply wf_exp_eq_sigma_sub; eassumption.
  - now apply Hne.
Qed.

Lemma neutral_snd_under_weakening : forall Γ i A B M n,
    wf_exp Γ (a_typ i) A ->
    wf_exp (A :: Γ) (a_typ i) B ->
    wf_exp Γ (a_sigma A B) M ->
    neutral_under_weakening Γ (a_sigma A B) M n ->
    neutral_under_weakening Γ (a_sub B (a_extend a_id (a_fst M))) (a_snd M) (d_snd n).
Proof.
  intros Γ i A B M n HA HB HM Hne Δ σ HW.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  pose proof (lift_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (substitute_type _ _ _ _ _ HQ HB) as HBs.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as HEQ.
  assert (Hσ : wf_exp Δ (a_sigma (a_sub A σ) (a_sub B (Syntax.q σ))) (a_sub M σ)).
  {
    eapply convert_expression; [eapply wf_exp_sub; eassumption | eapply wf_sigma; eassumption | exact HEQ].
  }
  pose proof (wf_fst _ _ _ _ _ HAs HBs Hσ) as Hfst.
  pose proof (wf_fst _ _ _ _ _ HA HB HM) as HF.
  pose proof (wf_exp_sub _ _ _ _ _ HS HF) as HFs.
  pose proof (wf_exp_eq_fst_sub _ _ _ _ _ _ _ HS HA HB HM) as HFe.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HFs) as HSf.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA Hfst) as HSf'.
  pose proof (instantiate_type _ _ _ _ HA HF) as HI.
  pose proof (substitute_type _ _ _ _ _ HS (substitute_type _ _ _ _ _ HI HB)) as Hgoal.
  assert (Hcod : wf_exp_eq Δ (a_typ i) (a_sub B (a_extend σ (a_sub (a_fst M) σ)))
      (a_sub B (a_extend σ (a_fst (a_sub M σ))))).
  {
    eapply substitute_type_equality; [exact HSf | | now apply reflexive_expression].
    eapply wf_sub_eq_extend_cong; [now apply reflexive_substitution | exact HA | exact HFe].
  }
  eapply quote_neutral_type_conversion; [exact Hgoal | |].
  - apply wf_exp_eq_sym; eapply wf_exp_eq_trans.
    + exact (substitute_instantiated_type _ _ _ _ _ _ _ _ HS HA HB HF).
    + exact Hcod.
  - eapply quote_neutral_conversion; [eapply wf_exp_eq_snd_sub; eassumption |].
    eapply quote_neutral_type_conversion.
    + exact (substitute_type _ _ _ _ _ HSf' HB).
    + exact (substitute_into_lift _ _ _ _ _ _ _ _ HS HA HB Hfst).
    + eapply quote_neutral_snd; [exact HAs | exact HBs |].
      eapply quote_neutral_type_conversion; [eapply wf_sigma; eassumption | exact HEQ |].
      now apply Hne.
Qed.

Record quotation_type Γ i A a : Prop := {
  quotation_well_formed : wf_exp Γ (a_typ i) A;
  quotation_of_type : type_under_weakening Γ i A a;
  quotation_of_neutral :
    forall Δ σ M n, weakening Δ Γ σ ->
      wf_exp Δ (a_sub A σ) M ->
      neutral_under_weakening Δ (a_sub A σ) M n ->
      quoted_term Δ (a_sub A σ) M a (d_neut a n)
}.

Lemma quote_neutral_at_type : forall Γ i A a M n, quotation_type Γ i A a ->
    wf_exp Γ A M -> neutral_under_weakening Γ A M n ->
    quoted_term Γ A M a (d_neut a n).
Proof.
  intros Γ i A a M n [HA HQ Href] HM HN.
  pose proof (expression_context _ _ _ HM) as HG.
  pose proof (wf_sub_id _ HG) as HID.
  pose proof (substitute_type _ _ _ _ _ HID HA) as HAid.
  pose proof (type_substitution_identity _ _ _ HA) as HE.
  assert (HMid : wf_exp Γ (a_sub A a_id) M).
  { eapply convert_expression; [exact HM | exact HAid | now apply wf_exp_eq_sym]. }
  assert (HNid : neutral_under_weakening Γ (a_sub A a_id) M n).
  { eapply convert_neutral_under_weakening; [exact HAid | exact (wf_exp_eq_sym _ _ _ _ HE) | exact HN]. }
  eapply quote_term_type_conversion; [exact HA | exact HE |].
  apply Href; [now apply weakening_identity | exact HMid | exact HNid].
Qed.

Lemma quotation_type_conversion : forall Γ i A B a,
    quotation_type Γ i A a -> wf_exp Γ (a_typ i) B -> wf_exp_eq Γ (a_typ i) A B ->
    quotation_type Γ i B a.
Proof.
  intros Γ i A B a [HA HQ Href] HB HE; constructor; [exact HB | |].
  - intros Δ σ HW.
    pose proof (weakening_is_typed _ _ _ HW) as HS.
    eapply quote_type_conversion; [eapply substitute_type_equality; [exact HS | now apply reflexive_substitution | exact (wf_exp_eq_sym _ _ _ _ HE)] | now apply HQ].
  - intros Δ σ M n HW HM HN.
    pose proof (weakening_is_typed _ _ _ HW) as HS.
    pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
    pose proof (substitute_type _ _ _ _ _ HS HB) as HBs.
    assert (HAB : wf_exp_eq Δ (a_typ i) (a_sub A σ) (a_sub B σ)).
    { eapply substitute_type_equality; [exact HS | now apply reflexive_substitution | exact HE]. }
    eapply quote_term_type_conversion; [exact HBs | exact HAB |].
    apply Href; [exact HW | |].
    + eapply convert_expression; [exact HM | exact HAs | exact (wf_exp_eq_sym _ _ _ _ HAB)].
    + eapply convert_neutral_under_weakening; [exact HAs | exact (wf_exp_eq_sym _ _ _ _ HAB) | exact HN].
Qed.

Lemma quotation_type_lift : forall Γ i j A a,
    quotation_type Γ i A a -> i <= j -> quotation_type Γ j A a.
Proof.
  intros Γ i j A a [HA HQ HR] Hle; constructor.
  - eapply cumulative_type; eassumption.
  - intros Δ σ HW.
    destruct (HQ _ _ HW) as (W & HR' & HE).
    exists W; split; [exact HR' |].
    eapply cumulative_type_equality; [|exact HE|exact Hle].
    exact (proj1 (substitution_contexts _ _ _ (weakening_is_typed _ _ _ HW))).
  - exact HR.
Qed.

Lemma quotation_type_nat : forall Γ, wf_ctx Γ -> quotation_type Γ 0 a_nat d_nat.
Proof.
  intros Γ HG; constructor; [now apply wf_nat | |].
  - intros Δ σ HW.
    pose proof (weakening_is_typed _ _ _ HW) as HS.
    eapply quote_type_conversion; [eapply wf_exp_eq_nat_sub; exact HS |].
    apply quote_type_nat; exact (proj1 (substitution_contexts _ _ _ HS)).
  - intros Δ σ M n HW HM HN.
    destruct (observe_neutral _ _ _ _ HM HN) as (W & HR & HE).
    exists (nf_neut W); split; [now apply read_nf_nat_neut | exact HE].
Qed.

Lemma quotation_type_universe : forall Γ i, wf_ctx Γ -> quotation_type Γ (S i) (a_typ i) (d_univ i).
Proof.
  intros Γ i HG; constructor; [now apply wf_typ | |].
  - intros Δ σ HW.
    pose proof (weakening_is_typed _ _ _ HW) as HS.
    eapply quote_type_conversion; [eapply wf_exp_eq_typ_sub; exact HS |].
    apply quote_type_universe; exact (proj1 (substitution_contexts _ _ _ HS)).
  - intros Δ σ M n HW HM HN.
    pose proof (weakening_is_typed _ _ _ HW) as HS.
    pose proof (proj1 (substitution_contexts _ _ _ HS)) as HD.
    pose proof (wf_exp_eq_typ_sub _ _ _ i HS) as HE.
    pose proof (wf_typ Δ i HD) as HU.
    apply (quote_term_type_conversion _ (S i) (a_typ i) _ _ _ _ (substitute_type _ _ _ _ _ HS (wf_typ _ _ HG)) (wf_exp_eq_sym _ _ _ _ HE)).
    apply quote_term_universe, quote_type_neutral.
    eapply quote_neutral_type_conversion; [exact HU | exact HE | now apply observe_neutral].
Qed.

Lemma quotation_type_opaque : forall Γ i A k n,
    wf_exp Γ (a_typ i) A ->
    neutral_under_weakening Γ (a_typ i) A n ->
    quotation_type Γ i A (d_neut k n).
Proof.
  intros Γ i A k n HA HN; constructor; [exact HA | |].
  - intros Δ σ HW.
    pose proof (weakening_is_typed _ _ _ HW) as HS.
    pose proof (proj1 (substitution_contexts _ _ _ HS)) as HD.
    apply quote_type_neutral.
    eapply quote_neutral_type_conversion; [now apply wf_typ | eapply wf_exp_eq_typ_sub; exact HS | now apply HN].
  - intros Δ σ M p HW HM HP.
    apply quote_term_opaque, observe_neutral; assumption.
Qed.

Lemma weaken_quotation_type : forall Γ Δ τ i A a,
    weakening Δ Γ τ -> quotation_type Γ i A a -> quotation_type Δ i (a_sub A τ) a.
Proof.
  intros Γ Δ τ i A a Hτ [HA HQ Href].
  pose proof (weakening_is_typed _ _ _ Hτ) as HT.
  pose proof (substitute_type _ _ _ _ _ HT HA) as HAt.
  constructor; [exact HAt | |].
  - intros Θ σ HW.
    pose proof (weakening_is_typed _ _ _ HW) as HS.
    eapply quote_type_conversion.
    + apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HS HT HA).
    + exact (HQ _ _ (weakening_compose _ _ _ _ _ HW Hτ)).
  - intros Θ σ M n HW HM HN.
    pose proof (weakening_is_typed _ _ _ HW) as HS.
    pose proof (weakening_compose _ _ _ _ _ HW Hτ) as HWS.
    pose proof (type_substitution_compose _ _ _ _ _ _ _ HS HT HA) as HE.
    pose proof (substitute_type _ _ _ _ _ HS HAt) as Hright.
    pose proof (substitute_type _ _ _ _ _ (weakening_is_typed _ _ _ HWS) HA) as Hleft.
    eapply quote_term_type_conversion; [exact Hright | exact HE |].
    apply Href; [exact HWS | |].
    + eapply convert_expression; [exact HM | exact Hleft | exact (wf_exp_eq_sym _ _ _ _ HE)].
    + eapply convert_neutral_under_weakening; [exact Hleft | exact (wf_exp_eq_sym _ _ _ _ HE) | exact HN].
Qed.

Lemma quote_neutral_everywhere : forall Γ i A a M n,
    quotation_type Γ i A a ->
    wf_exp Γ A M -> neutral_under_weakening Γ A M n ->
    term_under_weakening Γ A M a (d_neut a n).
Proof.
  intros Γ i A a M n HQ HM HN Δ σ HW.
  eapply (quotation_of_neutral _ _ _ _ HQ); [exact HW | |].
  - eapply wf_exp_sub; [exact (weakening_is_typed _ _ _ HW) | exact HM].
  - eapply weaken_neutral; eassumption.
Qed.

Lemma quotation_type_equality : forall Γ i A X Y a x y,
    quotation_type Γ i A a ->
    wf_exp Γ A X -> wf_exp Γ A Y ->
    term_under_weakening Γ A X a x -> term_under_weakening Γ A Y a y ->
    quotation_type Γ i (a_eq A X Y) (d_eq a x y).
Proof.
  intros Γ i A X Y a x y HQ HX HY HqX HqY.
  pose proof (quotation_well_formed _ _ _ _ HQ) as HA.
  constructor; [eapply wf_eq; eassumption | |].
  - intros Δ σ HW.
    pose proof (weakening_is_typed _ _ _ HW) as HS.
    eapply quote_type_conversion; [eapply wf_exp_eq_eq_sub; eassumption |].
    eapply quote_type_equality.
    + exact (quotation_of_type _ _ _ _ HQ _ _ HW).
    + exact (HqX _ _ HW).
    + exact (HqY _ _ HW).
  - intros Δ σ M n HW HM HN.
    apply quote_term_equality_neutral, observe_neutral; assumption.
Qed.

Definition dependent_quotation Γ i A B a ρ C :=
  forall Δ σ X x, weakening Δ Γ σ ->
    wf_exp Δ (a_sub A σ) X ->
    term_under_weakening Δ (a_sub A σ) X a x ->
    exists b, eval_exp C (extend_env ρ x) b /\
              quotation_type Δ i (a_sub B (a_extend σ X)) b.

Lemma fresh_argument_quotation : forall Γ Δ σ i A a,
    quotation_type Γ i A a ->
    weakening Δ Γ σ ->
    let Δ' := a_sub A σ :: Δ in
    let τ := a_compose σ a_weaken in
    let x := d_neut a (d_var (length Δ)) in
    weakening Δ' Γ τ /\
    wf_exp Δ' (a_sub A τ) (a_var 0) /\
    neutral_under_weakening Δ' (a_sub A τ) (a_var 0) (d_var (length Δ)) /\
    term_under_weakening Δ' (a_sub A τ) (a_var 0) a x.
Proof.
  intros Γ Δ σ i A a HQ HW; cbn zeta.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  pose proof (quotation_well_formed _ _ _ _ HQ) as HA.
  pose proof (proj1 (substitution_contexts _ _ _ HS)) as HD.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (wf_ctx_extend _ _ _ HD HAs) as HDb.
  pose proof (weakening_drop _ _ HDb) as Hlift.
  pose proof (weakening_compose _ _ _ _ _ Hlift HW) as Htau.
  pose proof (weakening_is_typed _ _ _ Hlift) as HT.
  pose proof (weaken_quotation_type _ _ _ _ _ _ Htau HQ) as HQt.
  pose proof (quotation_well_formed _ _ _ _ HQt) as HAt.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_compose _ _ _ _ _ _ _ HT HS HA)) as HE.
  assert (Hzero : wf_exp (a_sub A σ :: Δ) (a_sub A (a_compose σ a_weaken)) (a_var 0)).
  { eapply convert_expression; [now apply type_of_first_variable | exact HAt | exact HE]. }
  assert (Hn : neutral_under_weakening (a_sub A σ :: Δ) (a_sub A (a_compose σ a_weaken)) (a_var 0) (d_var (length Δ))).
  {
    eapply convert_neutral_under_weakening; [exact HAt | exact HE |].
    pose proof (variable_neutral_under_weakening _ _ _ HDb (here (a_sub A σ) Δ)) as HV.
    simpl in HV; now rewrite Nat.sub_0_r in HV.
  }
  split; [exact Htau |]. split; [exact Hzero |]. split; [exact Hn |].
  exact (quote_neutral_everywhere _ _ _ _ _ _ HQt Hzero Hn).
Qed.

Definition neutral_dependent_quotation Γ i A B a ρ C :=
  forall Δ σ X n, weakening Δ Γ σ ->
    wf_exp Δ (a_sub A σ) X ->
    neutral_under_weakening Δ (a_sub A σ) X n ->
    exists b, eval_exp C (extend_env ρ (d_neut a n)) b /\
              quotation_type Δ i (a_sub B (a_extend σ X)) b.

Lemma quotation_type_pi_from_neutrals : forall Γ i A B a ρ C,
    quotation_type Γ i A a ->
    wf_exp (A :: Γ) (a_typ i) B ->
    neutral_dependent_quotation Γ i A B a ρ C ->
    quotation_type Γ i (a_pi A B) (d_pi a ρ C).
Proof.
  intros Γ i A B a ρ C HQ HB HC.
  pose proof (quotation_well_formed _ _ _ _ HQ) as HA.
  constructor; [eapply wf_pi; eassumption | |].
  - intros Δ σ HW.
    pose proof (weakening_is_typed _ _ _ HW) as HS.
    destruct (fresh_argument_quotation _ _ _ _ _ _ HQ HW) as (Htau & HX & HN & Hqx).
    destruct (HC _ _ _ _ Htau HX HN) as (b & HBe & HBq).
    pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
    eapply quote_type_conversion; [eapply wf_exp_eq_pi_sub; eassumption |].
    eapply quote_type_pi.
    + exact HAs.
    + exact (quotation_of_type _ _ _ _ HQ _ _ HW).
    + exact HBe.
    + eapply observe_type; [exact (quotation_well_formed _ _ _ _ HBq) | exact (quotation_of_type _ _ _ _ HBq)].
  - intros Δ σ M n HW HM HN.
    pose proof (weakening_is_typed _ _ _ HW) as HS.
    pose proof (proj1 (substitution_contexts _ _ _ HS)) as HD.
    pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
    pose proof (wf_ctx_extend _ _ _ HD HAs) as HDb.
    pose proof (wf_sub_weaken _ _ HDb) as HWT.
    pose proof (lift_substitution _ _ _ _ _ HS HA) as HQS.
    pose proof (substitute_type _ _ _ _ _ HQS HB) as HBs.
    pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB) as HE.
    pose proof (wf_pi _ _ _ _ HAs HBs) as HP.
    pose proof (substitute_type _ _ _ _ _ HS (wf_pi _ _ _ _ HA HB)) as HPs.
    pose proof (convert_expression _ _ _ _ _ HM HP HE) as HMtyped.
    destruct (fresh_argument_quotation _ _ _ _ _ _ HQ HW) as (Htau & HX & HNzero & Hqx).
    destruct (HC _ _ _ _ Htau HX HNzero) as (b & HBe & HBq).
    pose proof (weakening_is_typed _ _ _ Htau) as HT.
    pose proof (substitute_type _ _ _ _ _ HT HA) as HAt.
    pose proof (lift_substitution _ _ _ _ _ HT HA) as HQT.
    pose proof (substitute_type _ _ _ _ _ HQT HB) as HBt.
    pose proof (wf_pi _ _ _ _ HAt HBt) as HPT.
    assert (HPTE : wf_exp_eq (a_sub A σ :: Δ) (a_typ i)
      (a_sub (a_sub (a_pi A B) σ) a_weaken)
      (a_pi (a_sub A (a_compose σ a_weaken)) (a_sub B (Syntax.q (a_compose σ a_weaken))))).
    {
      eapply wf_exp_eq_trans.
      - apply wf_exp_eq_sym; eapply type_substitution_compose; eassumption || (eapply wf_pi; eassumption).
      - eapply wf_exp_eq_pi_sub; eassumption.
    }
    assert (HMT : wf_exp (a_sub A σ :: Δ)
      (a_pi (a_sub A (a_compose σ a_weaken)) (a_sub B (Syntax.q (a_compose σ a_weaken)))) (a_sub M a_weaken)).
    {
      eapply convert_expression; [exact (wf_exp_sub _ _ _ _ _ HWT HM) | exact HPT | exact HPTE].
    }
    assert (Hnu : neutral_under_weakening (a_sub A σ :: Δ)
      (a_pi (a_sub A (a_compose σ a_weaken)) (a_sub B (Syntax.q (a_compose σ a_weaken)))) (a_sub M a_weaken) n).
    {
      eapply convert_neutral_under_weakening; [exact HPT | exact HPTE |].
      exact (weaken_neutral _ _ _ _ _ _ (weakening_drop _ _ HDb) HM HN).
    }
    pose proof (neutral_application_under_weakening _ _ _ _ _ _ _ _ _
      HAt HBt HMT HX Hnu Hqx) as Hbody.
    pose proof (substitute_into_lift _ _ _ _ _ _ _ _ HT HA HB HX) as HbodyE.
    assert (HBne : neutral_under_weakening (a_sub A σ :: Δ) (a_sub B (Syntax.q σ))
        (a_app (a_sub M a_weaken) (a_var 0))
        (d_app n (d_dom a (d_neut a (d_var (length Δ)))))).
    { eapply convert_neutral_under_weakening; [exact HBs | exact HbodyE | exact Hbody]. }
    assert (HBterm : wf_exp (a_sub A σ :: Δ) (a_sub B (Syntax.q σ)) (a_app (a_sub M a_weaken) (a_var 0))).
    {
      eapply convert_expression; [exact (wf_app _ _ _ _ _ _ HAt HBt HMT HX) | exact HBs | exact HbodyE].
    }
    pose proof (quote_neutral_at_type _ _ _ _ _ _ HBq HBterm HBne) as HbodyQ.
    eapply quote_term_type_conversion; [exact HPs | exact (wf_exp_eq_sym _ _ _ _ HE) |].
    eapply quote_term_pi.
    + exact HAs.
    + exact HBs.
    + exact HMtyped.
    + exact (quotation_of_type _ _ _ _ HQ _ _ HW).
    + apply eval_app_neut; exact HBe.
    + exact HBe.
    + exact HbodyQ.
Qed.

Lemma quotation_type_sigma_from_neutrals : forall Γ i A B a ρ C,
    quotation_type Γ i A a ->
    wf_exp (A :: Γ) (a_typ i) B ->
    neutral_dependent_quotation Γ i A B a ρ C ->
    quotation_type Γ i (a_sigma A B) (d_sigma a ρ C).
Proof.
  intros Γ i A B a ρ C HQ HB HC.
  pose proof (quotation_well_formed _ _ _ _ HQ) as HA.
  constructor; [eapply wf_sigma; eassumption | |].
  - intros Δ σ HW.
    pose proof (weakening_is_typed _ _ _ HW) as HS.
    destruct (fresh_argument_quotation _ _ _ _ _ _ HQ HW) as (Htau & HX & HN & Hqx).
    destruct (HC _ _ _ _ Htau HX HN) as (b & HBe & HBq).
    pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
    eapply quote_type_conversion; [eapply wf_exp_eq_sigma_sub; eassumption |].
    eapply quote_type_sigma.
    + exact HAs.
    + exact (quotation_of_type _ _ _ _ HQ _ _ HW).
    + exact HBe.
    + eapply observe_type; [exact (quotation_well_formed _ _ _ _ HBq) | exact (quotation_of_type _ _ _ _ HBq)].
  - intros Δ σ M n HW HM HN.
    pose proof (weakening_is_typed _ _ _ HW) as HS.
    pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
    pose proof (lift_substitution _ _ _ _ _ HS HA) as HQS.
    pose proof (substitute_type _ _ _ _ _ HQS HB) as HBs.
    pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as HE.
    pose proof (wf_sigma _ _ _ _ HAs HBs) as HP.
    pose proof (substitute_type _ _ _ _ _ HS (wf_sigma _ _ _ _ HA HB)) as HPs.
    pose proof (convert_expression _ _ _ _ _ HM HP HE) as HMtyped.
    pose proof (convert_neutral_under_weakening _ _ _ _ _ _ HP HE HN) as HNtyped.
    destruct (fresh_argument_quotation _ _ _ _ _ _ HQ HW) as (Htau & HX & HNzero & Hqx).
    destruct (HC _ _ _ _ Htau HX HNzero) as (b & HBe & HBq).
    pose proof (wf_fst _ _ _ _ _ HAs HBs HMtyped) as Hfst.
    pose proof (wf_snd _ _ _ _ _ HAs HBs HMtyped) as Hsnd.
    pose proof (neutral_fst_under_weakening _ _ _ _ _ _ HAs HBs HMtyped HNtyped) as HNfst.
    pose proof (neutral_snd_under_weakening _ _ _ _ _ _ HAs HBs HMtyped HNtyped) as HNsnd.
    pose proof (weaken_quotation_type _ _ _ _ _ _ HW HQ) as HQAσ.
    pose proof (quote_neutral_everywhere _ _ _ _ _ _ HQAσ Hfst HNfst) as HfstQ.
    destruct (HC _ _ _ _ HW Hfst HNfst) as (c & HCe & HCq).
    pose proof (substitute_into_lift _ _ _ _ _ _ _ _ HS HA HB Hfst) as HCtype.
    assert (Hnative : wf_exp Δ (a_typ i) (a_sub (a_sub B (Syntax.q σ)) (a_extend a_id (a_fst M)))).
    { eapply substitute_type; [exact (instantiate_type _ _ _ _ HAs Hfst) | exact HBs]. }
    pose proof (quotation_type_conversion _ _ _ _ _ HCq Hnative (wf_exp_eq_sym _ _ _ _ HCtype)) as HQsnd.
    eapply quote_term_type_conversion; [exact HPs | exact (wf_exp_eq_sym _ _ _ _ HE) |].
    eapply quote_term_sigma.
    + exact HAs.
    + exact HBs.
    + exact HMtyped.
    + exact (quotation_of_type _ _ _ _ HQ _ _ HW).
    + exact HBe.
    + eapply observe_type; [exact (quotation_well_formed _ _ _ _ HBq) | exact (quotation_of_type _ _ _ _ HBq)].
    + apply eval_fst_neut.
    + apply eval_snd_neut; exact HCe.
    + exact HCe.
    + eapply observe_term; [exact Hfst | exact HfstQ].
    + exact (quote_neutral_at_type _ _ _ _ _ _ HQsnd Hsnd HNsnd).
Qed.


Lemma quotation_type_pi : forall Γ i A B a ρ C,
    quotation_type Γ i A a ->
    wf_exp (A :: Γ) (a_typ i) B ->
    dependent_quotation Γ i A B a ρ C ->
    quotation_type Γ i (a_pi A B) (d_pi a ρ C).
Proof.
  intros Γ i A B a ρ C HQ HB HF.
  apply quotation_type_pi_from_neutrals; [exact HQ | exact HB |].
  intros Δ σ X n HW HX HN.
  apply HF; [exact HW | exact HX |].
  exact (quote_neutral_everywhere _ _ _ _ _ _ (weaken_quotation_type _ _ _ _ _ _ HW HQ) HX HN).
Qed.

Lemma quotation_type_sigma : forall Γ i A B a ρ C,
    quotation_type Γ i A a ->
    wf_exp (A :: Γ) (a_typ i) B ->
    dependent_quotation Γ i A B a ρ C ->
    quotation_type Γ i (a_sigma A B) (d_sigma a ρ C).
Proof.
  intros Γ i A B a ρ C HQ HB HF.
  apply quotation_type_sigma_from_neutrals; [exact HQ | exact HB |].
  intros Δ σ X n HW HX HN.
  apply HF; [exact HW | exact HX |].
  exact (quote_neutral_everywhere _ _ _ _ _ _ (weaken_quotation_type _ _ _ _ _ _ HW HQ) HX HN).
Qed.

Lemma variable_soundness_from_type_quotation : forall Γ x A ρ a i,
    wf_ctx Γ ->
    ctx_lookup x A Γ ->
    initial_env Γ ρ ->
    eval_exp A ρ a ->
    quotation_type Γ i A a ->
    exists W, nbe Γ (a_var x) A W /\ wf_exp_eq Γ A (a_var x) W.
Proof.
  intros Γ x A ρ a i HG HL HI HA HQ.
  destruct (initial_variable_value _ _ _ _ HI HL) as (b & HB & He).
  pose proof (exp_unique _ _ _ HB _ HA) as E; subst b.
  pose proof (wf_vlookup _ _ _ HG HL) as HM.
  pose proof (variable_neutral_under_weakening _ _ _ HG HL) as HN.
  destruct (quote_neutral_at_type _ _ _ _ _ _ HQ HM HN) as (W & HR & HE).
  exists W; split; [|exact HE].
  eapply nbe_run with (m := d_neut a (d_var (length Γ - x - 1))); [exact HI | exact HA | rewrite <- He; apply eval_exp_var | exact HR].
Qed.

Definition non_eta_type a : Prop :=
  match a with
  | d_pi _ _ _ | d_sigma _ _ _ => False
  | _ => True
  end.

Lemma variable_soundness_without_eta : forall Γ x A ρ a,
    wf_ctx Γ ->
    ctx_lookup x A Γ ->
    initial_env Γ ρ ->
    eval_exp A ρ a ->
    non_eta_type a ->
    exists W, nbe Γ (a_var x) A W /\ wf_exp_eq Γ A (a_var x) W.
Proof.
  intros Γ x A ρ a HG HL HI HA Hnon.
  destruct (initial_variable_value _ _ _ _ HI HL) as (b & HB & He).
  pose proof (exp_unique _ _ _ HB _ HA) as E; subst b.
  pose proof (wf_vlookup _ _ _ HG HL) as HM.
  pose proof (variable_neutral_under_weakening _ _ _ HG HL) as HN.
  destruct (observe_neutral _ _ _ _ HM HN) as (N & HR & HE).
  destruct fundamental_evaluation as (Hctx & _ & Hexp & _).
  destruct (proj1 (Hctx _ HG)) as (ρ' & HI' & Henv).
  pose proof (initial_env_unique _ _ HI _ HI') as E; subst ρ'.
  destruct (proj1 (Hexp _ _ _ HM) _ _ Henv) as (R & (a1 & a2 & H1 & H2 & [i HT]) & _).
  pose proof (exp_unique _ _ _ H1 _ HA) as E; subst a1.
  pose proof (exp_unique _ _ _ H2 _ HA) as E; subst a2.
  apply model_type_view in HT.
  assert (Hvar : eval_exp (a_var x) ρ (d_neut a (d_var (length Γ - x - 1)))) by (rewrite <- He; apply eval_exp_var).
  destruct a; cbn [type_view non_eta_type] in *; try contradiction;
    (exists (nf_neut N); split; [|exact HE]);
    (eapply nbe_run; [exact HI | exact HA | exact Hvar |]);
    first [apply read_nf_type, read_typ_neut | apply read_nf_nat_neut
          | apply read_nf_eq_neut | apply read_nf_neut]; exact HR.
Qed.

Definition function_action Γ A B a ρ C M m :=
  forall Δ σ X x, weakening Δ Γ σ ->
    wf_exp Δ (a_sub A σ) X ->
    term_under_weakening Δ (a_sub A σ) X a x ->
    exists b y,
      eval_exp C (extend_env ρ x) b /\ eval_app m x y /\
      quoted_term Δ (a_sub B (a_extend σ X)) (a_app (a_sub M σ) X) b y.

Lemma quote_function_action : forall Γ i A B a ρ C M m,
    quotation_type Γ i A a ->
    wf_exp (A :: Γ) (a_typ i) B ->
    wf_exp Γ (a_pi A B) M ->
    function_action Γ A B a ρ C M m ->
    term_under_weakening Γ (a_pi A B) M (d_pi a ρ C) m.
Proof.
  intros Γ i A B a ρ C M m HQ HB HM Hact Δ σ HW.
  pose proof (quotation_well_formed _ _ _ _ HQ) as HA.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  pose proof (proj1 (substitution_contexts _ _ _ HS)) as HD.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (wf_ctx_extend _ _ _ HD HAs) as HDb.
  pose proof (wf_sub_weaken _ _ HDb) as Hwk.
  pose proof (lift_substitution _ _ _ _ _ HS HA) as HQS.
  pose proof (substitute_type _ _ _ _ _ HQS HB) as HBs.
  pose proof (wf_pi _ _ _ _ HA HB) as HP.
  pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB) as HE.
  pose proof (wf_pi _ _ _ _ HAs HBs) as Hdirect.
  pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HMs.
  pose proof (convert_expression _ _ _ _ _ HMs Hdirect HE) as HMd.
  destruct (fresh_argument_quotation _ _ _ _ _ _ HQ HW) as (HT & HX & HXN & HXQ).
  destruct (Hact _ _ _ _ HT HX HXQ) as (b & y & HBe & Happly & Hbody).
  pose proof (weakening_is_typed _ _ _ HT) as HTsub.
  pose proof (substitute_type _ _ _ _ _ HTsub HA) as HAt.
  pose proof (lift_substitution _ _ _ _ _ HTsub HA) as HQt.
  pose proof (substitute_type _ _ _ _ _ HQt HB) as HBt.
  assert (Htyped : wf_exp_eq (a_sub A σ :: Δ)
    (a_pi (a_sub A (a_compose σ a_weaken)) (a_sub B (Syntax.q (a_compose σ a_weaken))))
    (a_sub (a_sub M σ) a_weaken) (a_sub M (a_compose σ a_weaken))).
  {
    eapply convert_equality.
    - apply wf_exp_eq_sym; eapply wf_exp_eq_sub_compose; eassumption.
    - eapply wf_pi; eassumption.
    - eapply wf_exp_eq_pi_sub; eassumption.
  }
  assert (HbodyE : wf_exp_eq (a_sub A σ :: Δ) (a_sub B (Syntax.q σ))
    (a_app (a_sub (a_sub M σ) a_weaken) (a_var 0)) (a_app (a_sub M (a_compose σ a_weaken)) (a_var 0))).
  {
    eapply convert_equality.
    - exact (wf_exp_eq_app_cong _ _ _ _ _ _ _ _ HAt HBt Htyped (reflexive_expression _ _ _ HX)).
    - exact HBs.
    - exact (substitute_into_lift _ _ _ _ _ _ _ _ HTsub HA HB HX).
  }
  eapply quote_term_type_conversion.
  - exact (substitute_type _ _ _ _ _ HS HP).
  - exact (wf_exp_eq_sym _ _ _ _ HE).
  - eapply quote_term_pi; [exact HAs | exact HBs | exact HMd | | exact Happly | exact HBe |].
    + exact (quotation_of_type _ _ _ _ HQ _ _ HW).
    + eapply quote_term_conversion; [exact HbodyE | exact Hbody].
Qed.

Definition pair_action Γ A B a ρ C M m :=
  forall Δ σ, weakening Δ Γ σ ->
    exists x y b,
      eval_fst m x /\ eval_snd m y /\ eval_exp C (extend_env ρ x) b /\
      quoted_term Δ (a_sub A σ) (a_fst (a_sub M σ)) a x /\
      quoted_term Δ (a_sub B (a_extend σ (a_fst (a_sub M σ)))) (a_snd (a_sub M σ)) b y.

Lemma quote_pair_action : forall Γ i A B a ρ C M m,
    quotation_type Γ i A a ->
    wf_exp (A :: Γ) (a_typ i) B ->
    dependent_quotation Γ i A B a ρ C ->
    wf_exp Γ (a_sigma A B) M ->
    pair_action Γ A B a ρ C M m ->
    term_under_weakening Γ (a_sigma A B) M (d_sigma a ρ C) m.
Proof.
  intros Γ i A B a ρ C M m HQ HB HC HM Hact Δ σ HW.
  pose proof (quotation_well_formed _ _ _ _ HQ) as HA.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (lift_substitution _ _ _ _ _ HS HA) as HQS.
  pose proof (substitute_type _ _ _ _ _ HQS HB) as HBs.
  pose proof (wf_sigma _ _ _ _ HA HB) as HP.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as HE.
  pose proof (wf_sigma _ _ _ _ HAs HBs) as Hdirect.
  pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HMs.
  pose proof (convert_expression _ _ _ _ _ HMs Hdirect HE) as HMd.
  destruct (fresh_argument_quotation _ _ _ _ _ _ HQ HW) as (HT & HX & HXN & HXQ).
  destruct (HC _ _ _ _ HT HX HXQ) as (b & HBe & HBq).
  destruct (Hact _ _ HW) as (x & y & b' & HF & HSnd & HBe' & Hqf & Hqs).
  pose proof (wf_fst _ _ _ _ _ HAs HBs HMd) as Hfst.
  pose proof (substitute_into_lift _ _ _ _ _ _ _ _ HS HA HB Hfst) as HsE.
  pose proof (instantiate_type _ _ _ _ HAs Hfst) as Hinst.
  pose proof (substitute_type _ _ _ _ _ Hinst HBs) as HsndB.
  eapply quote_term_type_conversion.
  - exact (substitute_type _ _ _ _ _ HS HP).
  - exact (wf_exp_eq_sym _ _ _ _ HE).
  - eapply quote_term_sigma; [exact HAs | exact HBs | exact HMd | | exact HBe | | exact HF | exact HSnd | exact HBe' | exact Hqf |].
    + exact (quotation_of_type _ _ _ _ HQ _ _ HW).
    + eapply observe_type; [exact (quotation_well_formed _ _ _ _ HBq) | exact (quotation_of_type _ _ _ _ HBq)].
    + eapply quote_term_type_conversion; [exact HsndB | exact (wf_exp_eq_sym _ _ _ _ HsE) | exact Hqs].
Qed.

Inductive natural_realizes (Γ : ctx) : exp -> domain -> Prop :=
| realizes_zero : wf_ctx Γ -> natural_realizes Γ a_zero d_zero
| realizes_succ : forall M m, natural_realizes Γ M m -> natural_realizes Γ (a_succ M) (d_succ m)
| realizes_neutral : forall M n,
    wf_exp Γ a_nat M ->
    neutral_under_weakening Γ a_nat M n ->
    natural_realizes Γ M (d_neut d_nat n)
| realizes_conversion : forall M N m,
    wf_exp Γ a_nat M -> wf_exp_eq Γ a_nat M N -> natural_realizes Γ N m ->
    natural_realizes Γ M m.

Lemma natural_realizes_typing : forall Γ M m, natural_realizes Γ M m -> wf_exp Γ a_nat M.
Proof. intros Γ M m H; induction H; eauto using wf_zero, wf_succ. Qed.

Lemma natural_realizes_quote : forall Γ M m,
    natural_realizes Γ M m -> quoted_term Γ a_nat M d_nat m.
Proof.
  intros Γ M m H; induction H.
  - now apply quote_term_zero.
  - now apply quote_term_succ.
  - apply quote_term_natural_neutral; now apply observe_neutral.
  - eapply quote_term_conversion; eassumption.
Qed.

Lemma natural_realizes_weaken : forall Γ M m, natural_realizes Γ M m ->
    forall Δ σ, weakening Δ Γ σ -> natural_realizes Δ (a_sub M σ) m.
Proof.
  intros Γ M m H; induction H; intros Δ σ HW;
    pose proof (weakening_is_typed _ _ _ HW) as HS;
    pose proof (proj1 (substitution_contexts _ _ _ HS)) as HD;
    pose proof (wf_nat Δ HD) as HNat;
    pose proof (wf_exp_eq_nat_sub _ _ _ HS) as HE.
  - eapply realizes_conversion.
    + eapply convert_expression; [eapply wf_exp_sub; [exact HS | now apply wf_zero] | exact HNat | exact HE].
    + exact (wf_exp_eq_zero_sub _ _ _ HS).
    + now apply realizes_zero.
  - pose proof (natural_realizes_typing _ _ _ H) as HM.
    eapply realizes_conversion.
    + eapply convert_expression; [eapply wf_exp_sub; [exact HS | now apply wf_succ] | exact HNat | exact HE].
    + exact (wf_exp_eq_succ_sub _ _ _ _ HS HM).
    + now apply realizes_succ, IHnatural_realizes.
  - apply realizes_neutral.
    + eapply convert_expression; [eapply wf_exp_sub; eassumption | exact HNat | exact HE].
    + eapply convert_neutral_under_weakening; [exact HNat | exact HE |].
      eapply weaken_neutral; eassumption.
  - eapply realizes_conversion.
    + eapply convert_expression; [eapply wf_exp_sub; eassumption | exact HNat | exact HE].
    + eapply convert_equality; [eapply wf_exp_eq_sub_cong; [eassumption | now apply reflexive_substitution] | exact HNat | exact HE].
    + now apply IHnatural_realizes.
Qed.

Lemma constant_family_quotation : forall Γ i A B a b ρ,
    wf_exp Γ (a_typ i) A -> quotation_type Γ i B b -> eval_exp B ρ b ->
    dependent_quotation Γ i A (a_sub B a_weaken) a ρ (a_sub B a_weaken).
Proof.
  intros Γ i A B a b ρ HA HQ HB Δ σ X x HW HX _.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  pose proof (quotation_well_formed _ _ _ _ HQ) as HBwf.
  pose proof (weaken_quotation_type _ _ _ _ _ _ HW HQ) as HQs.
  pose proof (substitute_weakening _ _ _ _ _ _ _ _ HS HA HBwf HX) as HE.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HX) as HC.
  pose proof (proj2 (substitution_contexts _ _ _ HC)) as HGA.
  pose proof (weaken_type _ _ _ _ HGA HBwf) as HBw.
  pose proof (substitute_type _ _ _ _ _ HC HBw) as HBn.
  exists b; split.
  - eapply eval_exp_sub; [apply eval_sub_weaken | exact HB].
  - eapply quotation_type_conversion; [exact HQs | exact HBn | exact (wf_exp_eq_sym _ _ _ _ HE)].
Qed.

Inductive simple_type : ctx -> nat -> exp -> Prop :=
| simple_natural : forall Γ, wf_ctx Γ -> simple_type Γ 0 a_nat
| simple_universe : forall Γ i, wf_ctx Γ -> simple_type Γ (S i) (a_typ i)
| simple_pi : forall Γ i A B,
    simple_type Γ i A -> simple_type Γ i B ->
    simple_type Γ i (a_pi A (a_sub B a_weaken))
| simple_sigma : forall Γ i A B,
    simple_type Γ i A -> simple_type Γ i B ->
    simple_type Γ i (a_sigma A (a_sub B a_weaken))
| simple_weaken : forall Γ Δ σ i A,
    weakening Γ Δ σ -> simple_type Δ i A -> simple_type Γ i (a_sub A σ)
| simple_lift : forall Γ i j A, i <= j -> simple_type Γ i A -> simple_type Γ j A.

Lemma evaluation_of_weakening : forall Γ Δ σ, weakening Γ Δ σ ->
    forall ρ, exists ρ', eval_sub σ ρ ρ'.
Proof.
  intros Γ Δ σ H; induction H; intros ρ.
  - eexists; apply eval_sub_id.
  - eexists; apply eval_sub_weaken.
  - destruct (IHweakening1 ρ) as (θ & Hθ).
    destruct (IHweakening2 θ) as (θ' & Hθ').
    eexists; eapply eval_sub_compose; eassumption.
Qed.

Lemma simple_type_quotation : forall Γ i A, simple_type Γ i A ->
    forall ρ, exists a, eval_exp A ρ a /\ quotation_type Γ i A a.
Proof.
  intros Γ i A H; induction H; intros ρ.
  - exists d_nat; split; [constructor | now apply quotation_type_nat].
  - exists (d_univ i); split; [constructor | now apply quotation_type_universe].
  - destruct (IHsimple_type1 ρ) as (a & HAe & HA).
    destruct (IHsimple_type2 ρ) as (b & HBe & HB).
    pose proof (quotation_well_formed _ _ _ _ HA) as HAwf.
    pose proof (quotation_well_formed _ _ _ _ HB) as HBwf.
    pose proof (wf_ctx_extend _ _ _ (expression_context _ _ _ HAwf) HAwf) as HGA.
    exists (d_pi a ρ (a_sub B a_weaken)); split; [now apply eval_exp_pi |].
    eapply quotation_type_pi; [exact HA | exact (weaken_type _ _ _ _ HGA HBwf) |].
    exact (constant_family_quotation _ _ _ _ _ _ _ HAwf HB HBe).
  - destruct (IHsimple_type1 ρ) as (a & HAe & HA).
    destruct (IHsimple_type2 ρ) as (b & HBe & HB).
    pose proof (quotation_well_formed _ _ _ _ HA) as HAwf.
    pose proof (quotation_well_formed _ _ _ _ HB) as HBwf.
    pose proof (wf_ctx_extend _ _ _ (expression_context _ _ _ HAwf) HAwf) as HGA.
    exists (d_sigma a ρ (a_sub B a_weaken)); split; [now apply eval_exp_sigma |].
    eapply quotation_type_sigma; [exact HA | exact (weaken_type _ _ _ _ HGA HBwf) |].
    exact (constant_family_quotation _ _ _ _ _ _ _ HAwf HB HBe).
  - destruct (evaluation_of_weakening _ _ _ H ρ) as (θ & Hθ).
    destruct (IHsimple_type θ) as (a & Ha & HQ).
    exists a; split; [eapply eval_exp_sub; eassumption | eapply weaken_quotation_type; eassumption].
  - destruct (IHsimple_type ρ) as (a & Ha & HQ).
    exists a; split; [exact Ha | eapply quotation_type_lift; eassumption].
Qed.

Lemma variable_soundness_at_simple_type : forall Γ x A i,
    wf_ctx Γ ->
    ctx_lookup x A Γ ->
    simple_type Γ i A ->
    exists W, nbe Γ (a_var x) A W /\ wf_exp_eq Γ A (a_var x) W.
Proof.
  intros Γ x A i HG HL HS.
  destruct fundamental_evaluation as (Hctx & _).
  destruct (proj1 (Hctx _ HG)) as (ρ & Hinit & Hrel).
  destruct (simple_type_quotation _ _ _ HS ρ) as (a & Ha & HQ).
  exact (variable_soundness_from_type_quotation _ _ _ _ _ _ HG HL Hinit Ha HQ).
Qed.

End SyntacticSoundness.


Module Gluing.

(* Glued types equip semantic types with typed quotation and reflection. *)

Import SoundnessSupport SyntacticSoundness.


(* Evaluation never inspects the numerical labels on neutral variables. *)
Inductive domain_shape : domain -> domain -> Prop :=
| ds_univ : forall i, domain_shape (d_univ i) (d_univ i)
| ds_nat : domain_shape d_nat d_nat
| ds_zero : domain_shape d_zero d_zero
| ds_succ : forall x y, domain_shape x y -> domain_shape (d_succ x) (d_succ y)
| ds_pi : forall a b ρ τ B, domain_shape a b ->
    (forall x, domain_shape (ρ x) (τ x)) ->
    domain_shape (d_pi a ρ B) (d_pi b τ B)
| ds_sigma : forall a b ρ τ B, domain_shape a b ->
    (forall x, domain_shape (ρ x) (τ x)) ->
    domain_shape (d_sigma a ρ B) (d_sigma b τ B)
| ds_fn : forall ρ τ M, (forall x, domain_shape (ρ x) (τ x)) ->
    domain_shape (d_fn ρ M) (d_fn τ M)
| ds_pair : forall x y x' y', domain_shape x x' -> domain_shape y y' ->
    domain_shape (d_pair x y) (d_pair x' y')
| ds_eq : forall a a' x x' y y', domain_shape a a' -> domain_shape x x' -> domain_shape y y' ->
    domain_shape (d_eq a x y) (d_eq a' x' y')
| ds_refl : forall x y, domain_shape x y -> domain_shape (d_refl x) (d_refl y)
| ds_neutral : forall a a' n n', domain_shape a a' -> neutral_shape n n' ->
    domain_shape (d_neut a n) (d_neut a' n')
with neutral_shape : domain_ne -> domain_ne -> Prop :=
| ns_var : forall l l', neutral_shape (d_var l) (d_var l')
| ns_app : forall n n' t t', neutral_shape n n' -> normal_shape t t' ->
    neutral_shape (d_app n t) (d_app n' t')
| ns_fst : forall n n', neutral_shape n n' -> neutral_shape (d_fst n) (d_fst n')
| ns_snd : forall n n', neutral_shape n n' -> neutral_shape (d_snd n) (d_snd n')
| ns_natrec : forall ρ τ B Z Z' S n n', (forall x, domain_shape (ρ x) (τ x)) ->
    domain_shape Z Z' -> neutral_shape n n' ->
    neutral_shape (d_natrec ρ B Z S n) (d_natrec τ B Z' S n')
| ns_eqrec : forall ρ τ a a' B BR x x' y y' n n',
    (forall k, domain_shape (ρ k) (τ k)) ->
    domain_shape a a' -> domain_shape x x' -> domain_shape y y' -> neutral_shape n n' ->
    neutral_shape (d_eqrec ρ a B BR x y n) (d_eqrec τ a' B BR x' y' n')
with normal_shape : domain_nf -> domain_nf -> Prop :=
| ns_normal : forall a a' m m', domain_shape a a' -> domain_shape m m' ->
    normal_shape (d_dom a m) (d_dom a' m').

Definition environment_shape (ρ τ : env) := forall x, domain_shape (ρ x) (τ x).

Scheme shape_domain_ind := Induction for domain Sort Prop
with shape_neutral_ind := Induction for domain_ne Sort Prop
with shape_normal_ind := Induction for domain_nf Sort Prop.
Combined Scheme shape_ind from shape_domain_ind, shape_neutral_ind, shape_normal_ind.

Lemma shape_reflexive :
  (forall a, domain_shape a a) /\ (forall n, neutral_shape n n) /\ (forall t, normal_shape t t).
Proof. apply shape_ind; intros; constructor; assumption. Qed.

Lemma shape_extend : forall ρ τ a b, environment_shape ρ τ -> domain_shape a b ->
    environment_shape (extend_env ρ a) (extend_env τ b).
Proof. intros ρ τ a b H HS [|x]; cbn; auto. Qed.

Lemma shape_fresh : forall a b l l', domain_shape a b ->
    domain_shape (d_neut a (d_var l)) (d_neut b (d_var l')).
Proof. intros; constructor; [assumption | constructor]. Qed.

Lemma shape_eval_fst : forall x y, eval_fst x y ->
    forall x', domain_shape x x' ->
      exists y', eval_fst x' y' /\ domain_shape y y'.
Proof.
  intros x y H; destruct H; intros z HZ; inversion HZ; subst.
  - eexists; split; [apply eval_fst_pair | eassumption].
  - match goal with H : domain_shape (d_sigma _ _ _) _ |- _ => inversion H; subst end.
    eexists; split; [apply eval_fst_neut | constructor; [eassumption | constructor; eassumption]].
Qed.

Create HintDb shapes.
#[local] Hint Constructors domain_shape neutral_shape normal_shape
  eval_exp eval_natrec eval_app eval_snd eval_eqrec eval_sub : shapes.
#[local] Hint Resolve shape_extend shape_fresh shape_eval_fst : shapes.

Ltac shape_witness :=
  repeat match goal with
  | IH : forall x, domain_shape ?a x -> forall τ, environment_shape ?ρ τ -> exists b, _,
      H : domain_shape ?a ?a' |- _ =>
      let E := fresh "Heval" in let S := fresh "Hshape" in
      let x := fresh "result" in
      destruct (IH a' _ H ltac:(solve [eauto 5 with shapes])) as (x & E & S); clear IH
  | IH : forall τ, environment_shape ?ρ τ -> exists b, _ |- _ =>
      let E := fresh "Heval" in let S := fresh "Hshape" in
      let x := fresh "result" in
      destruct (IH _ ltac:(solve [eauto 5 with shapes])) as (x & E & S); clear IH
  | IH : forall f, domain_shape ?a f -> forall x, domain_shape ?b x -> exists c, _,
      H : domain_shape ?a ?a', K : domain_shape ?b ?b' |- _ =>
      let E := fresh "Heval" in let S := fresh "Hshape" in
      let x := fresh "result" in
      destruct (IH a' H b' K) as (x & E & S); clear IH
  | IH : forall x, domain_shape ?a x -> exists b, _,
      H : domain_shape ?a ?a' |- _ =>
      let E := fresh "Heval" in let S := fresh "Hshape" in
      let x := fresh "result" in
      destruct (IH a' H) as (x & E & S); clear IH
  end.

Lemma shape_evaluation :
  (forall M ρ m, eval_exp M ρ m -> forall τ, environment_shape ρ τ ->
     exists n, eval_exp M τ n /\ domain_shape m n) /\
  (forall A Z S m ρ a, eval_natrec A Z S m ρ a ->
     forall n, domain_shape m n -> forall τ, environment_shape ρ τ ->
     exists b, eval_natrec A Z S n τ b /\ domain_shape a b) /\
  (forall f x y, eval_app f x y ->
     forall g, domain_shape f g -> forall z, domain_shape x z ->
     exists v, eval_app g z v /\ domain_shape y v) /\
  (forall x y, eval_snd x y -> forall x', domain_shape x x' ->
     exists y', eval_snd x' y' /\ domain_shape y y') /\
  (forall a B BR x y p ρ m, eval_eqrec a B BR x y p ρ m ->
     forall a' x' y' p' τ,
       domain_shape a a' -> domain_shape x x' -> domain_shape y y' -> domain_shape p p' ->
       environment_shape ρ τ ->
       exists v, eval_eqrec a' B BR x' y' p' τ v /\ domain_shape m v) /\
  (forall σ ρ θ, eval_sub σ ρ θ -> forall τ, environment_shape ρ τ ->
     exists θ', eval_sub σ τ θ' /\ environment_shape θ θ').
Proof.
  apply eval_mut_ind; intros;
    repeat match goal with
    | H : domain_shape (d_zero) _ |- _ => inversion H; subst; clear H
    | H : domain_shape (d_succ _) _ |- _ => inversion H; subst; clear H
    | H : domain_shape (d_fn _ _) _ |- _ => inversion H; subst; clear H
    | H : domain_shape (d_pair _ _) _ |- _ => inversion H; subst; clear H
    | H : domain_shape (d_refl _) _ |- _ => inversion H; subst; clear H
    | H : domain_shape (d_neut _ _) _ |- _ => inversion H; subst; clear H
    | H : domain_shape (d_pi _ _ _) _ |- _ => inversion H; subst; clear H
    | H : domain_shape (d_sigma _ _ _) _ |- _ => inversion H; subst; clear H
    end;
    shape_witness;
    try solve [eauto 6 with shapes].
  - destruct (H0 _ Hshape _ H1) as (w & Hw & HS); exists w; split; [eapply eval_exp_natrec; eassumption | exact HS].
  - destruct (shape_eval_fst _ _ e0 _ Hshape) as (w & Hw & HS); exists w; split; [eapply eval_exp_fst; eassumption | exact HS].
  - destruct (H3 _ _ _ _ _ Hshape2 Hshape1 Hshape0 Hshape H4) as (w & Hw & HS).
    exists w; split; [eapply eval_exp_eqrec; eassumption | exact HS].
  - destruct (H _ H4 _ H2) as (v & Hv & HS).
    destruct (H0 _ (shape_extend _ _ _ _ (shape_extend _ _ _ _ H2 H4) HS)) as (w & Hw & HSW).
    exists w; split; [eapply eval_natrec_succ; eassumption | exact HSW].
  - eexists; split; [apply eval_app_neut; exact Heval |].
    apply ds_neutral; [exact Hshape | apply ns_app; [exact H6 | now constructor]].
  - exists (drop_env τ); split; [constructor | intro k; exact (H (S k))].
Qed.

Definition same_shape_eval := proj1 shape_evaluation.
Definition same_shape_app := proj1 (proj2 (proj2 shape_evaluation)).
Definition same_shape_snd := proj1 (proj2 (proj2 (proj2 shape_evaluation))).

Ltac invert_shapes :=
  repeat match goal with
  | H : domain_shape (d_univ _) _ |- _ => inversion H; subst; clear H
  | H : domain_shape d_nat _ |- _ => inversion H; subst; clear H
  | H : domain_shape d_zero _ |- _ => inversion H; subst; clear H
  | H : domain_shape (d_succ _) _ |- _ => inversion H; subst; clear H
  | H : domain_shape (d_neut _ _) _ |- _ => inversion H; subst; clear H
  | H : domain_shape (d_pi _ _ _) _ |- _ => inversion H; subst; clear H
  | H : domain_shape (d_sigma _ _ _) _ |- _ => inversion H; subst; clear H
  | H : domain_shape (d_eq _ _ _) _ |- _ => inversion H; subst; clear H
  | H : domain_shape (d_refl _) _ |- _ => inversion H; subst; clear H
  | H : neutral_shape (d_var _) _ |- _ => inversion H; subst; clear H
  | H : neutral_shape (d_app _ _) _ |- _ => inversion H; subst; clear H
  | H : neutral_shape (d_fst _) _ |- _ => inversion H; subst; clear H
  | H : neutral_shape (d_snd _) _ |- _ => inversion H; subst; clear H
  | H : neutral_shape (d_natrec _ _ _ _ _) _ |- _ => inversion H; subst; clear H
  | H : neutral_shape (d_eqrec _ _ _ _ _ _ _) _ |- _ => inversion H; subst; clear H
  | H : normal_shape (d_dom _ _) _ |- _ => inversion H; subst; clear H
  end.

Ltac shape_reify_old t :=
  repeat match goal with
  | IH : forall r, domain_shape ?a r -> forall s, exists W, read_typ s r W,
      H : domain_shape ?a ?a' |- _ =>
      let N := fresh "T" in let E := fresh "HT" in
      destruct (IH a' H t) as (N & E); clear IH
  | IH : forall r, neutral_shape ?a r -> forall s, exists W, read_ne s r W,
      H : neutral_shape ?a ?a' |- _ =>
      let N := fresh "N" in let E := fresh "HN" in
      destruct (IH a' H t) as (N & E); clear IH
  | IH : forall r, normal_shape (d_dom ?a ?m) r -> forall s, exists W, read_nf s r W,
      H : domain_shape ?a ?a', K : domain_shape ?m ?m' |- _ =>
      let N := fresh "V" in let E := fresh "HV" in
      destruct (IH (d_dom a' m') (ns_normal _ _ _ _ H K) t) as (N & E); clear IH
  | IH : forall r, normal_shape ?a r -> forall s, exists W, read_nf s r W,
      H : normal_shape ?a ?a' |- _ =>
      let N := fresh "V" in let E := fresh "HV" in
      destruct (IH a' H t) as (N & E); clear IH
  end.

#[local] Hint Constructors read_nf read_ne read_typ : shapes.

Lemma shape_readback :
  (forall s a W, read_nf s a W -> forall b, normal_shape a b ->
     forall t, exists V, read_nf t b V) /\
  (forall s a W, read_ne s a W -> forall b, neutral_shape a b ->
     forall t, exists V, read_ne t b V) /\
  (forall s a W, read_typ s a W -> forall b, domain_shape a b ->
     forall t, exists V, read_typ t b V).
Proof.
  apply read_mut_ind; intros;
    invert_shapes;
    try solve [lazymatch goal with |- exists V, ?read ?t _ V => shape_reify_old t end; eauto 6 with shapes].
  - destruct (H _ (ns_normal _ _ _ _ ds_nat H1) t) as (V & HV); exists (nf_succ V); now constructor.
  - pose proof (shape_fresh _ _ s t H7) as Harg.
    destruct (same_shape_app _ _ _ e _ H6 _ Harg) as (v & Hv & Hsv).
    destruct (same_shape_eval _ _ _ e0 _ (shape_extend _ _ _ _ H8 Harg)) as (c & Hc & Hsc).
    destruct (H _ H7 t) as (D & HD).
    destruct (H0 _ (ns_normal _ _ _ _ Hsc Hsv) (S t)) as (V & HV).
    exists (nf_fn D V); eapply read_nf_fn; eassumption.
  - pose proof (shape_fresh _ _ s t H9) as Harg.
    destruct (same_shape_eval _ _ _ e _ (shape_extend _ _ _ _ H10 Harg)) as (c & Hc & Hsc).
    destruct (shape_eval_fst _ _ e0 _ H8) as (x & Hx & Hsx).
    destruct (same_shape_snd _ _ e1 _ H8) as (y & Hy & Hsy).
    destruct (same_shape_eval _ _ _ e2 _ (shape_extend _ _ _ _ H10 Hsx)) as (v & Hv & Hsv).
    destruct (H _ H9 t) as (D & HD).
    destruct (H0 _ Hsc (S t)) as (E & HE).
    destruct (H1 _ (ns_normal _ _ _ _ H9 Hsx) t) as (X & HX).
    destruct (H2 _ (ns_normal _ _ _ _ Hsv Hsy) t) as (Y & HY).
    exists (nf_pair X D Y E); eapply read_nf_sigma; eassumption.
  - pose proof (shape_fresh _ _ s t ds_nat) as Harg.
    pose proof (shape_extend _ _ _ _ H10 Harg) as Henv.
    destruct (same_shape_eval _ _ _ e _ Henv) as (c & Hc & Hsc).
    destruct (same_shape_eval _ _ _ e0 _ (shape_extend _ _ _ _ H10 ds_zero)) as (cz & Hcz & Hscz).
    destruct (same_shape_eval _ _ _ e1 _ (shape_extend _ _ _ _ H10 (ds_succ _ _ Harg))) as (cs & Hcs & Hscs).
    destruct (same_shape_eval _ _ _ e2 _ (shape_extend _ _ _ _ Henv (shape_fresh _ _ (S s) (S t) Hsc)))
      as (v & Hv & Hsv).
    destruct (H _ Hsc (S t)) as (D & HD).
    destruct (H0 _ (ns_normal _ _ _ _ Hscz H11) t) as (Vz & HVz).
    destruct (H1 _ (ns_normal _ _ _ _ Hscs Hsv) (S (S t))) as (Vs & HVs).
    destruct (H2 _ H12 t) as (P & HP).
    exists (ne_natrec D Vz Vs P); eapply read_ne_natrec; eassumption.
  - pose proof (shape_fresh _ _ s t H15) as Hx.
    pose proof (shape_fresh _ _ (S s) (S t) H15) as Hy.
    pose proof (shape_fresh _ _ (S (S s)) (S (S t)) (ds_eq _ _ _ _ _ _ H15 Hx Hy)) as Hp.
    pose proof (shape_extend _ _ _ _ H14 Hx) as HE.
    destruct (same_shape_eval _ _ _ e _ (shape_extend _ _ _ _ (shape_extend _ _ _ _ HE Hy) Hp))
      as (c & Hc & Hsc).
    destruct (same_shape_eval _ _ _ e0 _ (shape_extend _ _ _ _ (shape_extend _ _ _ _ HE Hx) (ds_refl _ _ Hx)))
      as (d & Hd & Hsd).
    destruct (same_shape_eval _ _ _ e1 _ HE) as (v & Hv & Hsv).
    destruct (H _ H15 t) as (D & HD).
    destruct (H0 _ (ns_normal _ _ _ _ H15 H16) t) as (X & HX).
    destruct (H1 _ (ns_normal _ _ _ _ H15 H17) t) as (Y & HY).
    destruct (H2 _ Hsc (S (S (S t)))) as (E & HEt).
    destruct (H3 _ (ns_normal _ _ _ _ Hsd Hsv) (S t)) as (V & HV).
    destruct (H4 _ H18 t) as (P & HP).
    exists (ne_eqrec D E V X Y P); eapply read_ne_eqrec; eassumption.
  - destruct (same_shape_eval _ _ _ e _ (shape_extend _ _ _ _ H7 (shape_fresh _ _ s t H6))) as (c & Hc & Hsc).
    destruct (H _ H6 t) as (D & HD).
    destruct (H0 _ Hsc (S t)) as (E & HE).
    exists (nf_pi D E); eapply read_typ_pi; eassumption.
  - destruct (same_shape_eval _ _ _ e _ (shape_extend _ _ _ _ H7 (shape_fresh _ _ s t H6))) as (c & Hc & Hsc).
    destruct (H _ H6 t) as (D & HD).
    destruct (H0 _ Hsc (S t)) as (E & HE).
    exists (nf_sigma D E); eapply read_typ_sigma; eassumption.
Qed.

Lemma neutral_reads_uniformly : forall s n N, read_ne s n N -> ne_related n n.
Proof.
  intros s n N H t.
  destruct (proj1 (proj2 shape_readback) _ _ _ H n (proj1 (proj2 shape_reflexive) n) t) as (V & HV).
  exists V; auto.
Qed.

Definition candidate := ctx -> sub -> exp -> domain -> Prop.
Definition universe_candidate := ctx -> exp -> domain -> Prop.

Definition semantic_member a m : Prop :=
  exists k R, at_type k a a R /\ R m m.

Lemma semantic_neutral_member : forall k a n S, at_type k a a S ->
    ne_related n n -> semantic_member a (d_neut a n).
Proof.
  intros k a n S H Hn; exists k, S; split; [exact H |].
  exact (proj2 (proj2 (model_readback _ (universes_valid k) _ _ _ H)) _ _ Hn).
Qed.

Definition candidate_invariants Γ A a (K : candidate) :=
  forall Δ σ M m, weakening Δ Γ σ ->
    K Δ σ M m ->
    wf_exp Δ (a_sub A σ) M /\ semantic_member a m /\
    term_under_weakening Δ (a_sub A σ) M a m.

Definition observed_candidate (Γ : ctx) A a (K : candidate) : candidate :=
  fun Δ σ M m =>
    wf_exp Δ (a_sub A σ) M /\ semantic_member a m /\
    term_under_weakening Δ (a_sub A σ) M a m /\ K Δ σ M m.

Definition neutral_candidate (Γ : ctx) A (is_value : domain -> domain_ne -> Prop) : candidate :=
  fun Δ σ M m => exists n, is_value m n /\ neutral_under_weakening Δ (a_sub A σ) M n.

Definition callable (R : candidate) (T : ctx -> sub -> exp -> domain -> candidate)
    (Γ : ctx) (A B : exp) (ρ : env) C : candidate :=
  fun Δ σ M m =>
    forall Θ τ X x, weakening Θ Δ τ -> R Θ (a_compose σ τ) X x ->
      exists b y,
        eval_exp C (extend_env ρ x) b /\ eval_app m x y /\
        T Θ (a_compose σ τ) X x Θ a_id (a_app (a_sub M τ) X) y.

Definition projectable (R : candidate) (T : ctx -> sub -> exp -> domain -> candidate)
    (Γ : ctx) (A B : exp) (ρ : env) C : candidate :=
  fun Δ σ M m =>
    forall Θ τ, weakening Θ Δ τ ->
      exists x y b,
        eval_fst m x /\ eval_snd m y /\ eval_exp C (extend_env ρ x) b /\
        R Θ (a_compose σ τ) (a_fst (a_sub M τ)) x /\
        T Θ (a_compose σ τ) (a_fst (a_sub M τ)) x Θ a_id (a_snd (a_sub M τ)) y.

Definition reflexive_candidate (R : candidate) (Γ : ctx) A X Y (a x y : domain) : candidate :=
  fun Δ σ M m =>
    (exists e n, m = d_neut e n /\ neutral_under_weakening Δ (a_sub (a_eq A X Y) σ) M n) \/
    (exists Z z, m = d_refl z /\ R Δ σ Z z /\
      wf_exp_eq Δ (a_sub A σ) Z (a_sub X σ) /\
      wf_exp_eq Δ (a_sub A σ) Z (a_sub Y σ) /\
      wf_exp_eq Δ (a_sub (a_eq A X Y) σ) M (a_refl (a_sub A σ) Z)).

Inductive glued_type (U : list universe_candidate) : ctx -> nat -> exp -> domain -> candidate -> Prop :=
| glued_type_nat : forall Γ, wf_ctx Γ ->
    glued_type U Γ 0 a_nat d_nat
      (observed_candidate Γ a_nat d_nat
        (fun Δ σ M m => exists r, natural_realizes Δ M r /\ nat_rel r m))
| glued_type_univ : forall Γ i P, wf_ctx Γ -> nth_error U i = Some P ->
    glued_type U Γ (S i) (a_typ i) (d_univ i)
      (observed_candidate Γ (a_typ i) (d_univ i) (fun Δ σ M m => P Δ M m))
| glued_type_neutral : forall Γ i A k n,
    wf_exp Γ (a_typ i) A ->
    neutral_under_weakening Γ (a_typ i) A n ->
    glued_type U Γ i A (d_neut k n)
      (observed_candidate Γ A (d_neut k n)
        (neutral_candidate Γ A (fun m n => exists k, m = d_neut k n)))
| glued_type_pi : forall Γ i A B a ρ C R T S,
    at_type i (d_pi a ρ C) (d_pi a ρ C) S ->
    glued_type U Γ i A a R ->
    wf_exp (A :: Γ) (a_typ i) B ->
    (forall Δ σ X x, weakening Δ Γ σ -> R Δ σ X x ->
       exists b, eval_exp C (extend_env ρ x) b) ->
    (forall Δ σ X x, weakening Δ Γ σ -> R Δ σ X x ->
       forall b, eval_exp C (extend_env ρ x) b ->
       glued_type U Δ i (a_sub B (a_extend σ X)) b (T Δ σ X x)) ->
    glued_type U Γ i (a_pi A B) (d_pi a ρ C)
      (observed_candidate Γ (a_pi A B) (d_pi a ρ C) (callable R T Γ A B ρ C))
| glued_type_sigma : forall Γ i A B a ρ C R T S,
    at_type i (d_sigma a ρ C) (d_sigma a ρ C) S ->
    glued_type U Γ i A a R ->
    wf_exp (A :: Γ) (a_typ i) B ->
    (forall Δ σ X x, weakening Δ Γ σ -> R Δ σ X x ->
       exists b, eval_exp C (extend_env ρ x) b) ->
    (forall Δ σ X x, weakening Δ Γ σ -> R Δ σ X x ->
       forall b, eval_exp C (extend_env ρ x) b ->
       glued_type U Δ i (a_sub B (a_extend σ X)) b (T Δ σ X x)) ->
    glued_type U Γ i (a_sigma A B) (d_sigma a ρ C)
      (observed_candidate Γ (a_sigma A B) (d_sigma a ρ C) (projectable R T Γ A B ρ C))
| glued_type_eq : forall Γ i A X Y a x y R S,
    at_type i (d_eq a x y) (d_eq a x y) S ->
    glued_type U Γ i A a R ->
    wf_exp Γ A X -> wf_exp Γ A Y ->
    (forall Δ σ, weakening Δ Γ σ -> R Δ σ (a_sub X σ) x) ->
    (forall Δ σ, weakening Δ Γ σ -> R Δ σ (a_sub Y σ) y) ->
    glued_type U Γ i (a_eq A X Y) (d_eq a x y)
      (observed_candidate Γ (a_eq A X Y) (d_eq a x y)
        (reflexive_candidate R Γ A X Y a x y))
| glued_type_convert : forall Γ i A B a R,
    glued_type U Γ i A a R ->
    wf_exp Γ (a_typ i) B ->
    wf_exp_eq Γ (a_typ i) A B ->
    glued_type U Γ i B a R
| glued_type_shift : forall Γ Δ i A a R τ,
    glued_type U Γ i A a R -> weakening Δ Γ τ ->
    glued_type U Δ i (a_sub A τ) a (fun Θ σ => R Θ (a_compose τ σ))
| glued_type_extensional : forall Γ i A a R K,
    glued_type U Γ i A a R ->
    (forall Δ σ M m, weakening Δ Γ σ -> (R Δ σ M m <-> K Δ σ M m)) ->
    glued_type U Γ i A a K
| glued_type_cumulative : forall Γ i j A a R,
    glued_type U Γ i A a R -> i <= j -> glued_type U Γ j A a R
| glued_type_transport : forall Γ i A a b R S,
    glued_type U Γ i A a R -> at_type i a b S ->
    glued_type U Γ i A b (fun Δ σ M n => exists m, R Δ σ M m /\ S m n).

Definition universe_invariants (U : list universe_candidate) :=
  forall j P, nth_error U j = Some P ->
    (forall Γ M m, P Γ M m -> quotation_type Γ j M m) /\
    (forall Γ M k n, wf_exp Γ (a_typ j) M ->
       neutral_under_weakening Γ (a_typ j) M n -> P Γ M (d_neut k n)).

Lemma glued_type_well_formed : forall U Γ i A a R,
    glued_type U Γ i A a R -> wf_exp Γ (a_typ i) A.
Proof.
  intros U Γ i A a R H; induction H;
    eauto using wf_nat, wf_typ, wf_pi, wf_sigma, wf_eq, substitute_type, weakening_is_typed, cumulative_type.
Qed.

Lemma candidate_has_invariants : forall U Γ i A a R,
    glued_type U Γ i A a R -> candidate_invariants Γ A a R.
Proof.
  intros U Γ i A a R H; induction H; try (intros Δ σ M m HW HR; exact (conj (proj1 HR) (conj (proj1 (proj2 HR)) (proj1 (proj2 (proj2 HR)))))).
  - intros Δ σ M m HW HR.
    destruct (IHglued_type _ _ _ _ HW HR) as (HM & HS & HQ).
    pose proof (weakening_is_typed _ _ _ HW) as Hσ.
    pose proof (substitute_type _ _ _ _ _ Hσ H0) as HB.
    assert (HE : wf_exp_eq Δ (a_typ i) (a_sub A σ) (a_sub B σ)).
    { eapply substitute_type_equality; [exact Hσ | now apply reflexive_substitution | exact H1]. }
    split; [eapply convert_expression; eassumption |].
    split; [exact HS | eapply convert_term_under_weakening; eassumption].
  - intros Θ σ M m HW HR.
    pose proof (weakening_compose _ _ _ _ _ HW H0) as Hcomp.
    destruct (IHglued_type _ _ _ _ Hcomp HR) as (HM & HS & HQ).
    pose proof (glued_type_well_formed _ _ _ _ _ _ H) as HA.
    pose proof (weakening_is_typed _ _ _ H0) as Hτ.
    pose proof (weakening_is_typed _ _ _ HW) as Hσ.
    pose proof (substitute_type _ _ _ _ _ Hσ (substitute_type _ _ _ _ _ Hτ HA)) as HB.
    pose proof (type_substitution_compose _ _ _ _ _ _ _ Hσ Hτ HA) as HE.
    split; [eapply convert_expression; eassumption |].
    split; [exact HS | eapply convert_term_under_weakening; eassumption].
  - intros Δ σ M m HW HK.
    exact (IHglued_type _ _ _ _ HW (proj2 (H0 _ _ _ _ HW) HK)).
  - exact IHglued_type.
  - intros Δ σ M n HW (m & HR & HS).
    destruct (IHglued_type _ _ _ _ HW HR) as (HM & _ & HQ).
    split; [exact HM |].
    split.
    + exists i, S; split; [exact (at_type_self_r _ _ _ _ H0) |].
      eapply per_right; [exact (at_type_per _ _ _ _ H0) | exact HS].
    + intros Θ τ HT.
      eapply quote_term_semantic_conversion; [exact H0 | exact HS | now apply HQ].
Qed.


Lemma typed_neutral_self : forall Γ A M n,
    wf_exp Γ A M -> neutral_under_weakening Γ A M n -> ne_related n n.
Proof.
  intros Γ A M n HM HN.
  destruct (observe_neutral _ _ _ _ HM HN) as (N & HR & HE).
  eapply neutral_reads_uniformly; exact HR.
Qed.

Lemma glued_type_semantic : forall U Γ i A a R,
    glued_type U Γ i A a R -> exists S, at_type i a a S.
Proof.
  intros U Γ i A a R H; induction H; try assumption; try (eexists; eassumption).
  - exists nat_rel; apply model_nat.
  - exists (type_rel (universes i)); apply typed_universe_value.
  - exists opaque_rel; apply model_opaque; eapply typed_neutral_self; eassumption.
  - destruct IHglued_type as (S & HS); exists S; eapply model_type_lift; eassumption.
  - exists S; exact (at_type_self_r _ _ _ _ H0).
Qed.

Definition candidate_reflects Γ A a (R : candidate) :=
  forall Δ σ M n, weakening Δ Γ σ ->
    wf_exp Δ (a_sub A σ) M ->
    neutral_under_weakening Δ (a_sub A σ) M n ->
    R Δ σ M (d_neut a n).

Lemma quote_reflected_all : forall Γ Δ σ i A a M n, quotation_type Γ i A a ->
    weakening Δ Γ σ -> wf_exp Δ (a_sub A σ) M ->
    neutral_under_weakening Δ (a_sub A σ) M n ->
    term_under_weakening Δ (a_sub A σ) M a (d_neut a n).
Proof.
  intros; eapply quote_neutral_everywhere; [eapply weaken_quotation_type; eassumption | eassumption | eassumption].
Qed.

Lemma reflect_at_identity : forall Γ i A a R M n,
    quotation_type Γ i A a ->
    candidate_reflects Γ A a R ->
    wf_exp Γ A M -> neutral_under_weakening Γ A M n ->
    R Γ a_id M (d_neut a n).
Proof.
  intros Γ i A a R M n HQ Href HM HN.
  pose proof (expression_context _ _ _ HM) as HG.
  pose proof (quotation_well_formed _ _ _ _ HQ) as HA.
  pose proof (substitute_type _ _ _ _ _ (wf_sub_id _ HG) HA) as HAi.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_identity _ _ _ HA)) as HE.
  apply Href; [now apply weakening_identity | eapply convert_expression; eassumption |].
  eapply convert_neutral_under_weakening; eassumption.
Qed.

Lemma prepare_neutral_binder : forall Γ Δ Θ i A B σ τ M n (C : exp -> exp -> exp),
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    weakening Δ Γ σ -> weakening Θ Δ τ ->
    (forall Γ i A B, wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
       wf_exp Γ (a_typ i) (C A B)) ->
    (forall Γ Δ σ i A B, wf_sub Γ Δ σ -> wf_exp Δ (a_typ i) A ->
       wf_exp (A :: Δ) (a_typ i) B ->
       wf_exp_eq Γ (a_typ i) (a_sub (C A B) σ) (C (a_sub A σ) (a_sub B (Syntax.q σ)))) ->
    wf_exp Δ (a_sub (C A B) σ) M ->
    neutral_under_weakening Δ (a_sub (C A B) σ) M n ->
    let s := a_compose σ τ in
    wf_exp Θ (a_typ i) (a_sub A s) /\
    wf_exp (a_sub A s :: Θ) (a_typ i) (a_sub B (Syntax.q s)) /\
    wf_exp Θ (C (a_sub A s) (a_sub B (Syntax.q s))) (a_sub M τ) /\
    neutral_under_weakening Θ (C (a_sub A s) (a_sub B (Syntax.q s))) (a_sub M τ) n.
Proof.
  intros Γ Δ Θ i A B σ τ M n C HA HB HS HT Hkind Hprop HM HN; cbn zeta.
  pose proof (weakening_is_typed _ _ _ HS) as Hσ.
  pose proof (weakening_is_typed _ _ _ HT) as Hτ.
  pose proof (wf_sub_compose _ _ _ _ _ Hτ Hσ) as Hs.
  pose proof (substitute_type _ _ _ _ _ Hs HA) as HAs.
  pose proof (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ Hs HA) HB) as HBs.
  pose proof (Hkind _ _ _ _ HAs HBs) as HCs.
  assert (HE : wf_exp_eq Θ (a_typ i) (a_sub (a_sub (C A B) σ) τ)
      (C (a_sub A (a_compose σ τ)) (a_sub B (Syntax.q (a_compose σ τ))))).
  {
    eapply wf_exp_eq_trans.
    - apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ Hτ Hσ (Hkind _ _ _ _ HA HB)).
    - exact (Hprop _ _ _ _ _ _ Hs HA HB).
  }
  split; [exact HAs |]. split; [exact HBs |]. split.
  - exact (convert_expression _ _ _ _ _ (wf_exp_sub _ _ _ _ _ Hτ HM) HCs HE).
  - eapply convert_neutral_under_weakening; [exact HCs | exact HE |].
    eapply weaken_neutral; eassumption.
Qed.

Lemma apply_neutral_after_weakening : forall Γ Δ Θ i A B σ τ M X a x n,
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    weakening Δ Γ σ -> weakening Θ Δ τ ->
    wf_exp Δ (a_sub (a_pi A B) σ) M ->
    neutral_under_weakening Δ (a_sub (a_pi A B) σ) M n ->
    wf_exp Θ (a_sub A (a_compose σ τ)) X ->
    term_under_weakening Θ (a_sub A (a_compose σ τ)) X a x ->
    let Bx := a_sub B (a_extend (a_compose σ τ) X) in
    wf_exp Θ Bx (a_app (a_sub M τ) X) /\
    neutral_under_weakening Θ Bx (a_app (a_sub M τ) X) (d_app n (d_dom a x)).
Proof.
  intros Γ Δ Θ i A B σ τ M X a x n HA HB HS HT HM HN HX HQ; cbn zeta.
  destruct (prepare_neutral_binder _ _ _ _ _ _ _ _ _ _ a_pi
      HA HB HS HT wf_pi wf_exp_eq_pi_sub HM HN) as (HAs & HBs & HTM & HTN).
  pose proof (weakening_is_typed _ _ _ (weakening_compose _ _ _ _ _ HT HS)) as Hs.
  pose proof (wf_sub_extend _ _ _ _ _ _ Hs HA HX) as HE.
  pose proof (substitute_type _ _ _ _ _ HE HB) as HBx.
  pose proof (substitute_into_lift _ _ _ _ _ _ _ _ Hs HA HB HX) as HBxe.
  split.
  - exact (convert_expression _ _ _ _ _ (wf_app _ _ _ _ _ _ HAs HBs HTM HX) HBx HBxe).
  - eapply convert_neutral_under_weakening; [exact HBx | exact HBxe |].
    exact (neutral_application_under_weakening _ _ _ _ _ _ _ _ _ HAs HBs HTM HX HTN HQ).
Qed.

Lemma project_neutral_after_weakening : forall Γ Δ Θ i A B σ τ M n,
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    weakening Δ Γ σ -> weakening Θ Δ τ ->
    wf_exp Δ (a_sub (a_sigma A B) σ) M ->
    neutral_under_weakening Δ (a_sub (a_sigma A B) σ) M n ->
    let X := a_fst (a_sub M τ) in
    let Y := a_snd (a_sub M τ) in
    let s := a_compose σ τ in
    wf_exp Θ (a_sub A s) X /\ neutral_under_weakening Θ (a_sub A s) X (d_fst n) /\
    wf_exp Θ (a_sub B (a_extend s X)) Y /\
    neutral_under_weakening Θ (a_sub B (a_extend s X)) Y (d_snd n).
Proof.
  intros Γ Δ Θ i A B σ τ M n HA HB HS HT HM HN; cbn zeta.
  destruct (prepare_neutral_binder _ _ _ _ _ _ _ _ _ _ a_sigma
      HA HB HS HT wf_sigma wf_exp_eq_sigma_sub HM HN) as (HAs & HBs & HTM & HTN).
  pose proof (wf_fst _ _ _ _ _ HAs HBs HTM) as HX.
  pose proof (weakening_is_typed _ _ _ (weakening_compose _ _ _ _ _ HT HS)) as Hs.
  pose proof (wf_sub_extend _ _ _ _ _ _ Hs HA HX) as HE.
  pose proof (substitute_type _ _ _ _ _ HE HB) as HBx.
  pose proof (substitute_into_lift _ _ _ _ _ _ _ _ Hs HA HB HX) as HBxe.
  split; [exact HX |]. split.
  - eapply neutral_fst_under_weakening; eassumption.
  - split.
    + exact (convert_expression _ _ _ _ _ (wf_snd _ _ _ _ _ HAs HBs HTM) HBx HBxe).
    + eapply convert_neutral_under_weakening; [exact HBx | exact HBxe |].
      exact (neutral_snd_under_weakening _ _ _ _ _ _ HAs HBs HTM HTN).
Qed.

Lemma quotation_type_semantic_transport : forall Γ i A a b k S,
    quotation_type Γ i A a -> at_type k a b S -> quotation_type Γ i A b.
Proof.
  intros Γ i A a b k S [HA HQ HR] HT; constructor; [exact HA | |].
  - intros Δ σ HW; eapply quote_type_semantic_conversion; [exact HT | now apply HQ].
  - intros Δ σ M n HW HM HN.
    eapply quote_term_semantic_conversion; [exact HT | | exact (HR _ _ _ _ HW HM HN)].
    destruct (model_readback _ (universes_valid k) _ _ _ HT) as [_ [_ Href]].
    apply Href; eapply typed_neutral_self; eassumption.
Qed.

Lemma quoted_candidate_reflects : forall U Γ i A a R,
    universe_invariants U ->
    glued_type U Γ i A a R ->
    quotation_type Γ i A a /\ candidate_reflects Γ A a R.
Proof.
  intros U Γ i A a R HU H.
  induction H as
    [Γ HG
    |Γ j P HG HP
    |Γ j A k n HA HN
    |Γ j A B a ρ C R T S HS HA IHA HB HC HT IHT
    |Γ j A B a ρ C R T S HS HA IHA HB HC HT IHT
    |Γ j A X Y a x y R S HS HA IHA HX HY HRX HRY
    |Γ j A B a R HA IHA HB HE
    |Γ Δ j A a R τ HA IHA HT
    |Γ j A a R K HA IHA HE
    |Γ j k A a R HA IHA Hle
    |Γ j A a b R S HA IHA HS].
  - pose proof (quotation_type_nat Γ HG) as HQ.
    split; [exact HQ |].
    intros Δ σ M n HW HM HN.
    split; [exact HM |]. split.
    + eapply semantic_neutral_member; [exact (model_nat (universes 0)) | eapply typed_neutral_self; eassumption].
    + split; [eapply quote_reflected_all; eassumption |].
      pose proof (weakening_is_typed _ _ _ HW) as Hσ.
      pose proof (wf_nat _ (expression_context _ _ _ HM)) as HNat.
      pose proof (wf_exp_eq_nat_sub _ _ _ Hσ) as HE.
      exists (d_neut d_nat n); split.
      * apply realizes_neutral.
        -- eapply convert_expression; eassumption.
        -- eapply convert_neutral_under_weakening; eassumption.
      * apply nat_rel_neut; exact (typed_neutral_self _ _ _ _ HM HN).
  - pose proof (quotation_type_universe Γ j HG) as HQ.
    split; [exact HQ |].
    intros Δ σ M n HW HM HN.
    split; [exact HM |]. split.
    + eapply semantic_neutral_member; [apply typed_universe_value | eapply typed_neutral_self; eassumption].
    + split; [eapply quote_reflected_all; eassumption |].
      destruct (HU _ _ HP) as [_ HR].
      pose proof (weakening_is_typed _ _ _ HW) as Hσ.
      pose proof (wf_typ _ j (expression_context _ _ _ HM)) as HTyp.
      pose proof (wf_exp_eq_typ_sub _ _ _ j Hσ) as HE.
      apply HR.
      * eapply convert_expression; eassumption.
      * eapply convert_neutral_under_weakening; eassumption.
  - pose proof (quotation_type_opaque Γ j A k n HA HN) as HQ.
    split; [exact HQ |].
    intros Δ σ M p HW HM HP.
    split; [exact HM |]. split.
    + eapply (semantic_neutral_member j _ _ opaque_rel).
      * apply model_opaque. exact (typed_neutral_self _ _ _ _ HA HN).
      * eapply typed_neutral_self; eassumption.
    + split; [eapply quote_reflected_all; eassumption |].
      exists p; split; [exists (d_neut k n); reflexivity | exact HP].
  - destruct IHA as [HQ HR].
    pose proof (quotation_well_formed _ _ _ _ HQ) as HAw.
    assert (HQF : neutral_dependent_quotation Γ j A B a ρ C).
    {
      intros Δ σ M n HW HM HN.
      pose proof (HR _ _ _ _ HW HM HN) as HK.
      destruct (HC _ _ _ _ HW HK) as (b & Hb).
      exists b; split; [exact Hb | exact (proj1 (IHT _ _ _ _ HW HK _ Hb))].
    }
    pose proof (quotation_type_pi_from_neutrals _ _ _ _ _ _ _ HQ HB HQF) as HQP.
    split; [exact HQP |].
    intros Δ σ M n HW HM HN.
    pose proof (typed_neutral_self _ _ _ _ HM HN) as Hn.
    split; [exact HM |]. split.
    + exact (semantic_neutral_member _ _ _ _ HS Hn).
    + split; [eapply quote_reflected_all; eassumption |].
      intros Θ τ X x Hτ HX.
      pose proof (weakening_compose _ _ _ _ _ Hτ HW) as Hshift.
      destruct (candidate_has_invariants _ _ _ _ _ _ HA _ _ _ _ Hshift HX) as (HXw & (k & V & HV & HRx) & HXq).
      destruct (apply_neutral_after_weakening _ _ _ _ _ _ _ _ _ _ _ _ _
        HAw HB HW Hτ HM HN HXw HXq) as (Happ & Hnp).
      destruct (HC _ _ _ _ Hshift HX) as (b & Hb).
      destruct (IHT _ _ _ _ Hshift HX _ Hb) as [HQx Href].
      exists b, (d_neut b (d_app n (d_dom a x))).
      split; [exact Hb |]. split; [now apply eval_app_neut |].
      exact (reflect_at_identity _ _ _ _ _ _ _ HQx Href Happ Hnp).
  - destruct IHA as [HQ HR].
    pose proof (quotation_well_formed _ _ _ _ HQ) as HAw.
    assert (HQF : neutral_dependent_quotation Γ j A B a ρ C).
    {
      intros Δ σ M n HW HM HN.
      pose proof (HR _ _ _ _ HW HM HN) as HK.
      destruct (HC _ _ _ _ HW HK) as (b & Hb).
      exists b; split; [exact Hb | exact (proj1 (IHT _ _ _ _ HW HK _ Hb))].
    }
    pose proof (quotation_type_sigma_from_neutrals _ _ _ _ _ _ _ HQ HB HQF) as HQP.
    split; [exact HQP |].
    intros Δ σ M n HW HM HN.
    pose proof (typed_neutral_self _ _ _ _ HM HN) as Hn.
    split; [exact HM |]. split.
    + exact (semantic_neutral_member _ _ _ _ HS Hn).
    + split; [eapply quote_reflected_all; eassumption |].
      intros Θ τ Hτ.
      pose proof (weakening_compose _ _ _ _ _ Hτ HW) as Hshift.
      destruct (project_neutral_after_weakening _ _ _ _ _ _ _ _ _ _
        HAw HB HW Hτ HM HN) as (HXw & HNf & HYw & HNs).
      pose proof (HR _ _ _ _ Hshift HXw HNf) as HX.
      destruct (HC _ _ _ _ Hshift HX) as (b & Hb).
      destruct (IHT _ _ _ _ Hshift HX _ Hb) as [HQx Href].
      exists (d_neut a (d_fst n)), (d_neut b (d_snd n)), b.
      split; [apply eval_fst_neut |]. split; [apply eval_snd_neut; exact Hb |].
      split; [exact Hb |]. split; [exact HX |].
      exact (reflect_at_identity _ _ _ _ _ _ _ HQx Href HYw HNs).
  - destruct IHA as [HQ HR].
    assert (HXq : term_under_weakening Γ A X a x).
    {
      intros Δ σ HW.
      destruct (candidate_has_invariants _ _ _ _ _ _ HA _ _ _ _ HW (HRX _ _ HW)) as (HM & HT & HQM).
      exact (observe_term _ _ _ _ _ HM HQM).
    }
    assert (HYq : term_under_weakening Γ A Y a y).
    {
      intros Δ σ HW.
      destruct (candidate_has_invariants _ _ _ _ _ _ HA _ _ _ _ HW (HRY _ _ HW)) as (HM & HT & HQM).
      exact (observe_term _ _ _ _ _ HM HQM).
    }
    pose proof (quotation_type_equality _ _ _ _ _ _ _ _ HQ HX HY HXq HYq) as HQE.
    split; [exact HQE |].
    intros Δ σ M n HW HM HN.
    split; [exact HM |]. split.
    + eapply semantic_neutral_member; [exact HS | eapply typed_neutral_self; eassumption].
    + split; [eapply quote_reflected_all; eassumption |].
      left; exists (d_eq a x y), n; auto.
  - destruct IHA as [HQ HR].
    split; [eapply quotation_type_conversion; eassumption |].
    intros Δ σ M n HW HM HN.
    pose proof (weakening_is_typed _ _ _ HW) as Hσ.
    pose proof (substitute_type _ _ _ _ _ Hσ (quotation_well_formed _ _ _ _ HQ)) as HAs.
    assert (Hback : wf_exp_eq Δ (a_typ j) (a_sub B σ) (a_sub A σ)).
    { eapply substitute_type_equality; [exact Hσ | now apply reflexive_substitution | now apply wf_exp_eq_sym]. }
    apply HR; [exact HW | eapply convert_expression; eassumption | eapply convert_neutral_under_weakening; eassumption].
  - destruct IHA as [HQ HR].
    split; [eapply weaken_quotation_type; eassumption |].
    intros Θ σ M n HW HM HN.
    pose proof (weakening_is_typed _ _ _ HT) as Hτ.
    pose proof (weakening_is_typed _ _ _ HW) as Hσ.
    pose proof (wf_sub_compose _ _ _ _ _ Hσ Hτ) as Hcomp.
    pose proof (quotation_well_formed _ _ _ _ HQ) as HAw.
    pose proof (substitute_type _ _ _ _ _ Hcomp HAw) as HAs.
    pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_compose _ _ _ _ _ _ _ Hσ Hτ HAw)) as HE.
    apply HR; [eapply weakening_compose; eassumption | eapply convert_expression; eassumption | eapply convert_neutral_under_weakening; eassumption].
  - destruct IHA as [HQ HR].
    split; [exact HQ |].
    intros Δ σ M n HW HM HN.
    apply HE; [exact HW | now apply HR].
  - destruct IHA as [HQ HR]; split; [eapply quotation_type_lift; eassumption | exact HR].
  - destruct IHA as [HQ HR].
    split; [eapply quotation_type_semantic_transport; eassumption |].
    intros Δ σ M n HW HM HN.
    exists (d_neut a n); split; [now apply HR |].
    destruct (model_readback _ (universes_valid j) _ _ _ HS) as [_ [_ Href]].
    apply Href; eapply typed_neutral_self; eassumption.
Qed.

Definition gluing_universe (U : list universe_candidate) : universe_candidate :=
  fun Γ A a => exists R, glued_type U Γ (length U) A a R.

Fixpoint gluing_universes (k : nat) : list universe_candidate :=
  match k with
  | 0 => nil
  | S j => let U := gluing_universes j in U ++ (gluing_universe U :: nil)
  end.

Lemma gluing_universes_length : forall k, length (gluing_universes k) = k.
Proof. induction k; simpl; [reflexivity | rewrite length_app, IHk; simpl; lia]. Qed.

Lemma gluing_universes_quote : forall k, universe_invariants (gluing_universes k).
Proof.
  induction k as [|k IH]; intros i P H; [destruct i; discriminate |].
  simpl in H.
  destruct (Nat.lt_ge_cases i (length (gluing_universes k))) as [Hlt | Hge].
  - apply (IH i P); now rewrite nth_error_app1 in H.
  - rewrite nth_error_app2 in H by exact Hge.
    assert (E : i - length (gluing_universes k) = 0).
    { assert (Hbound : i - length (gluing_universes k) < length (gluing_universe (gluing_universes k) :: nil)).
      { apply nth_error_Some; rewrite H; discriminate. }
      simpl in Hbound; lia. }
    rewrite E in H; injection H as <-.
    assert (i = length (gluing_universes k)) by lia; subst i.
    split.
    + intros Γ A a (R & HR); exact (proj1 (quoted_candidate_reflects _ _ _ _ _ _ IH HR)).
    + intros Γ A a n HA HN; eexists; exact (glued_type_neutral _ _ _ _ _ _ HA HN).
Qed.

Lemma type_gluing_syntax_equality : forall U Γ Δ i j A B a b R T Θ σ τ k V,
    universe_invariants U ->
    glued_type U Γ i A a R -> glued_type U Δ j B b T ->
    weakening Θ Γ σ -> weakening Θ Δ τ -> at_type k a b V ->
    wf_exp_eq Θ (a_typ (Nat.max i j)) (a_sub A σ) (a_sub B τ).
Proof.
  intros U Γ Δ i j A B a b R T Θ σ τ k V HU HA HB Hσ Hτ Hk.
  destruct (quoted_candidate_reflects _ _ _ _ _ _ HU HA) as [HQA _].
  destruct (quoted_candidate_reflects _ _ _ _ _ _ HU HB) as [HQB _].
  destruct (quotation_of_type _ _ _ _ HQA _ _ Hσ) as (W & HR & HE).
  destruct (quotation_of_type _ _ _ _ HQB _ _ Hτ) as (W' & HR' & HE').
  destruct (quote_type_semantic_conversion _ _ _ _ _ _ _ Hk (ex_intro _ W (conj HR HE))) as (W'' & HR'' & HE'').
  pose proof (proj2 (proj2 readback_unique) _ _ _ HR' _ HR'') as E; subst W''.
  pose proof (proj1 (substitution_contexts _ _ _ (weakening_is_typed _ _ _ Hσ))) as HΘ.
  eapply wf_exp_eq_trans.
  - exact (cumulative_type_equality _ _ _ _ _ HΘ HE'' (Nat.le_max_l i j)).
  - apply wf_exp_eq_sym; exact (cumulative_type_equality _ _ _ _ _ HΘ HE' (Nat.le_max_r i j)).
Qed.

Lemma type_gluing_move_term : forall U Γ Δ i j A B a b R T Θ σ τ k V M,
    universe_invariants U ->
    glued_type U Γ i A a R -> glued_type U Δ j B b T ->
    weakening Θ Γ σ -> weakening Θ Δ τ -> at_type k a b V ->
    wf_exp Θ (a_sub A σ) M -> wf_exp Θ (a_sub B τ) M.
Proof.
  intros U Γ Δ i j A B a b R T Θ σ τ k V M HU HA HB Hσ Hτ Hk HM.
  eapply convert_expression; [exact HM | | exact (type_gluing_syntax_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HU HA HB Hσ Hτ Hk)].
  eapply cumulative_type.
  - eapply substitute_type; [exact (weakening_is_typed _ _ _ Hτ) | exact (glued_type_well_formed _ _ _ _ _ _ HB)].
  - apply Nat.le_max_r.
Qed.

Lemma type_gluing_move_eq : forall U Γ Δ i j A B a b R T Θ σ τ k V M N,
    universe_invariants U ->
    glued_type U Γ i A a R -> glued_type U Δ j B b T ->
    weakening Θ Γ σ -> weakening Θ Δ τ -> at_type k a b V ->
    wf_exp_eq Θ (a_sub A σ) M N -> wf_exp_eq Θ (a_sub B τ) M N.
Proof.
  intros U Γ Δ i j A B a b R T Θ σ τ k V M N HU HA HB Hσ Hτ Hk HM.
  eapply convert_equality; [exact HM | | exact (type_gluing_syntax_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HU HA HB Hσ Hτ Hk)].
  eapply cumulative_type.
  - eapply substitute_type; [exact (weakening_is_typed _ _ _ Hτ) | exact (glued_type_well_formed _ _ _ _ _ _ HB)].
  - apply Nat.le_max_r.
Qed.

Lemma candidates_observed_related : forall U Γ Δ i j A B a b R T Θ σ τ k V M N m n,
    universe_invariants U ->
    glued_type U Γ i A a R -> glued_type U Δ j B b T ->
    weakening Θ Γ σ -> weakening Θ Δ τ ->
    at_type k a b V -> V m n ->
    wf_exp Θ (a_sub B τ) N -> wf_exp_eq Θ (a_sub A σ) M N ->
    term_under_weakening Θ (a_sub A σ) M a m ->
    wf_exp Θ (a_sub B τ) N /\ semantic_member b n /\ term_under_weakening Θ (a_sub B τ) N b n.
Proof.
  intros U Γ Δ i j A B a b R T Θ σ τ k V M N m n HU HA HB Hσ Hτ Hk HV HN HE HQ.
  split; [exact HN |]. split.
  - exists k, V; split; [exact (at_type_self_r _ _ _ _ Hk) |].
    eapply per_right; [exact (at_type_per _ _ _ _ Hk) | exact HV].
  - eapply convert_term_under_weakening.
    + eapply cumulative_type.
      * eapply substitute_type; [exact (weakening_is_typed _ _ _ Hτ) | exact (glued_type_well_formed _ _ _ _ _ _ HB)].
      * apply Nat.le_max_r.
    + exact (type_gluing_syntax_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HU HA HB Hσ Hτ Hk).
    + eapply term_under_weakening_conversion; [exact (wf_exp_eq_sym _ _ _ _ HE) |].
      intros Ξ υ HW; eapply quote_term_semantic_conversion; [exact Hk | exact HV | now apply HQ].
Qed.

Definition aligned Γ A a (R : candidate) Δ B b (T : candidate) :=
  forall Θ σ τ M N m n k V,
    weakening Θ Γ σ -> weakening Θ Δ τ ->
    wf_exp Θ (a_sub A σ) M -> wf_exp Θ (a_sub B τ) N ->
    wf_exp_eq Θ (a_sub A σ) M N -> wf_exp_eq Θ (a_sub B τ) M N ->
    at_type k a b V -> V m n ->
    (R Θ σ M m <-> T Θ τ N n).

Lemma aligned_sym : forall Γ A a R Δ B b T,
    aligned Γ A a R Δ B b T -> aligned Δ B b T Γ A a R.
Proof.
  intros Γ A a R Δ B b T H Θ τ σ N M n m k V Hτ Hσ HN HM HNE HME HE HV.
  apply iff_sym.
  eapply H, (proj1 (at_type_per _ _ _ _ HE)); eauto using wf_exp_eq_sym, at_type_sym.
Qed.

Lemma aligned_convert_right : forall Γ A a R Δ B B' b T i,
    wf_exp Δ (a_typ i) B ->
    wf_exp_eq Δ (a_typ i) B B' ->
    aligned Γ A a R Δ B b T ->
    aligned Γ A a R Δ B' b T.
Proof.
  intros Γ A a R Δ B B' b T i HB HE H Θ σ τ M N m n k V Hσ Hτ HM HN HME HNE Hk HV.
  pose proof (weakening_is_typed _ _ _ Hτ) as HT.
  pose proof (substitute_type _ _ _ _ _ HT HB) as HBs.
  assert (HBEs : wf_exp_eq Θ (a_typ i) (a_sub B' τ) (a_sub B τ)).
  { eapply substitute_type_equality; [exact HT | now apply reflexive_substitution | now apply wf_exp_eq_sym]. }
  eapply H; try eassumption; eauto using convert_expression, convert_equality.
Qed.

Lemma aligned_shift_right : forall Γ A a R Ξ Δ B b T υ i,
    wf_exp Δ (a_typ i) B ->
    weakening Ξ Δ υ ->
    aligned Γ A a R Δ B b T ->
    aligned Γ A a R Ξ (a_sub B υ) b (fun Θ τ => T Θ (a_compose υ τ)).
Proof.
  intros Γ A a R Ξ Δ B b T υ i HB Hυ H Θ σ τ M N m n k V Hσ Hτ HM HN HME HNE Hk HV.
  pose proof (weakening_compose _ _ _ _ _ Hτ Hυ) as Hcomp.
  pose proof (weakening_is_typed _ _ _ Hcomp) as HC.
  pose proof (substitute_type _ _ _ _ _ HC HB) as HBs.
  pose proof (type_substitution_compose _ _ _ _ _ _ _
    (weakening_is_typed _ _ _ Hτ) (weakening_is_typed _ _ _ Hυ) HB) as HEs.
  eapply H; try eassumption; eauto using convert_expression, convert_equality, wf_exp_eq_sym.
Qed.

Lemma aligned_extensional_right : forall Γ A a R Δ B b T K,
    (forall Θ τ M m, weakening Θ Δ τ -> (T Θ τ M m <-> K Θ τ M m)) ->
    aligned Γ A a R Δ B b T ->
    aligned Γ A a R Δ B b K.
Proof.
  intros Γ A a R Δ B b T K HE H Θ σ τ M N m n k V Hσ Hτ HM HN HME HNE Hk HV.
  etransitivity; [eapply H; eassumption | now apply HE].
Qed.

Lemma aligned_semantic_right : forall Γ A a R Δ B b c T j S,
    at_type j b c S ->
    aligned Γ A a R Δ B b T ->
    aligned Γ A a R Δ B c (fun Θ τ M n => exists m, T Θ τ M m /\ S m n).
Proof.
  intros Γ A a R Δ B b c T j S HS H Θ σ τ M N m n k V Hσ Hτ HM HN HME HNE Hk HV.
  pose proof (at_type_sym _ _ _ _ HS) as Hrev.
  pose proof (at_type_trans _ _ _ _ _ _ _ Hk Hrev) as Htrans.
  pose proof (at_type_coherent_r _ _ _ _ _ _ _ Hk HS) as Hcoherence.
  destruct (at_type_per _ _ _ _ Hk) as [HSym HTrans].
  split.
  - intros HR; exists n; split.
    + apply (proj1 (H _ _ _ _ _ _ _ _ _ Hσ Hτ HM HN HME HNE Htrans HV)), HR.
    + exact (proj1 (Hcoherence _ _) (HTrans _ _ _ (HSym _ _ HV) HV)).
  - intros (p & HT & HR).
    assert (Hrel : V m p) by exact (HTrans _ _ _ HV (HSym _ _ (proj2 (Hcoherence _ _) HR))).
    apply (proj2 (H _ _ _ _ _ _ _ _ _ Hσ Hτ HM HN HME HNE Htrans Hrel)), HT.
Qed.

Lemma compatible_neutral : forall Γ A M n n',
    ne_related n n' -> neutral_under_weakening Γ A M n ->
    neutral_under_weakening Γ A M n'.
Proof.
  intros Γ A M n n' Hn HN Δ σ HW.
  destruct (HN _ _ HW) as (W & HR & HE).
  destruct (Hn (length Δ)) as (V & HV & HV').
  pose proof (read_ne_unique _ _ _ HR _ HV) as <-.
  now exists W.
Qed.

Lemma canonical_binder_after_weakening : forall Γ Δ Θ i A B σ τ M N (C : exp -> exp -> exp),
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    weakening Δ Γ σ -> weakening Θ Δ τ ->
    (forall Γ i A B, wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
       wf_exp Γ (a_typ i) (C A B)) ->
    (forall Γ Δ σ i A B, wf_sub Γ Δ σ -> wf_exp Δ (a_typ i) A ->
       wf_exp (A :: Δ) (a_typ i) B ->
       wf_exp_eq Γ (a_typ i) (a_sub (C A B) σ) (C (a_sub A σ) (a_sub B (Syntax.q σ)))) ->
    wf_exp Δ (a_sub (C A B) σ) M ->
    wf_exp_eq Δ (a_sub (C A B) σ) M N ->
    let s := a_compose σ τ in
    wf_exp Θ (a_typ i) (a_sub A s) /\
    wf_exp (a_sub A s :: Θ) (a_typ i) (a_sub B (Syntax.q s)) /\
    wf_exp Θ (C (a_sub A s) (a_sub B (Syntax.q s))) (a_sub M τ) /\
    wf_exp_eq Θ (C (a_sub A s) (a_sub B (Syntax.q s))) (a_sub M τ) (a_sub N τ).
Proof.
  intros Γ Δ Θ i A B σ τ M N C HA HB HS HT Hkind Hprop HM HN; cbn zeta.
  pose proof (weakening_is_typed _ _ _ HS) as Hσ.
  pose proof (weakening_is_typed _ _ _ HT) as Hτ.
  pose proof (wf_sub_compose _ _ _ _ _ Hτ Hσ) as Hs.
  pose proof (substitute_type _ _ _ _ _ Hs HA) as HAs.
  pose proof (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ Hs HA) HB) as HBs.
  pose proof (Hkind _ _ _ _ HAs HBs) as HCs.
  assert (HE : wf_exp_eq Θ (a_typ i) (a_sub (a_sub (C A B) σ) τ)
      (C (a_sub A (a_compose σ τ)) (a_sub B (Syntax.q (a_compose σ τ))))).
  {
    eapply wf_exp_eq_trans.
    - apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ Hτ Hσ (Hkind _ _ _ _ HA HB)).
    - exact (Hprop _ _ _ _ _ _ Hs HA HB).
  }
  split; [exact HAs |]. split; [exact HBs |]. split.
  - exact (convert_expression _ _ _ _ _ (wf_exp_sub _ _ _ _ _ Hτ HM) HCs HE).
  - eapply convert_equality; [eapply wf_exp_eq_sub_cong; [exact HN | now apply reflexive_substitution]
                          | exact HCs | exact HE].
Qed.

Lemma at_lifted_instance : forall Θ Δ σ A B X i j,
    wf_sub Θ Δ σ -> wf_exp Δ (a_typ i) A -> wf_exp (A :: Δ) (a_typ j) B ->
    wf_exp Θ (a_sub A σ) X ->
    wf_exp Θ (a_typ j) (a_sub B (a_extend σ X)) /\
    wf_exp_eq Θ (a_typ j) (a_sub (a_sub B (Syntax.q σ)) (a_extend a_id X))
                         (a_sub B (a_extend σ X)).
Proof.
  intros Θ Δ σ A B X i j HS HA HB HX.
  split.
  - exact (substitute_type _ _ _ _ _ (wf_sub_extend _ _ _ _ _ _ HS HA HX) HB).
  - exact (substitute_into_lift _ _ _ _ _ _ _ _ HS HA HB HX).
Qed.

Lemma preserve_at_id : forall Θ i A M N,
    wf_exp Θ (a_typ i) A ->
    wf_exp Θ A M -> wf_exp_eq Θ A M N ->
    wf_exp Θ (a_sub A a_id) M /\ wf_exp_eq Θ (a_sub A a_id) M N.
Proof.
  intros Θ i A M N HA HM HE.
  pose proof (wf_sub_id _ (expression_context _ _ _ HA)) as Hid.
  pose proof (substitute_type _ _ _ _ _ Hid HA) as HAi.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_identity _ _ _ HA)) as Hback.
  split; [exact (convert_expression _ _ _ _ _ HM HAi Hback)
         | exact (convert_equality _ _ _ _ _ _ HE HAi Hback)].
Qed.

Definition covariant_action Γ A a (R : candidate) Δ B b (T : candidate) :=
  forall Θ σ τ M N m n k V,
    weakening Θ Γ σ -> weakening Θ Δ τ ->
    wf_exp Θ (a_sub A σ) M -> wf_exp Θ (a_sub B τ) N ->
    wf_exp_eq Θ (a_sub A σ) M N -> wf_exp_eq Θ (a_sub B τ) M N ->
    at_type k a b V -> V m n -> R Θ σ M m -> T Θ τ N n.

Lemma two_actions_align : forall Γ A a R Δ B b T,
    covariant_action Γ A a R Δ B b T ->
    covariant_action Δ B b T Γ A a R ->
    aligned Γ A a R Δ B b T.
Proof.
  intros Γ A a R Δ B b T HC HR Θ σ τ M N m n k V Hσ Hτ HM HN HME HNE HV Hrel.
  split.
  - eapply HC; eassumption.
  - eapply HR; eauto using wf_exp_eq_sym, at_type_sym.
    exact (proj1 (at_type_per _ _ _ _ HV) _ _ Hrel).
Qed.

Definition families_align Γ (i : nat) B (a : domain) (ρ : env) C (R : candidate)
    (T : ctx -> sub -> exp -> domain -> candidate)
    Δ (j : nat) B' (a' : domain) (ρ' : env) C' (R' : candidate)
    (T' : ctx -> sub -> exp -> domain -> candidate) :=
  forall Θ σ τ X X' x x' b b',
    weakening Θ Γ σ -> weakening Θ Δ τ ->
    R Θ σ X x -> R' Θ τ X' x' ->
    eval_exp C (extend_env ρ x) b -> eval_exp C' (extend_env ρ' x') b' ->
    aligned Θ (a_sub B (a_extend σ X)) b (T Θ σ X x)
            Θ (a_sub B' (a_extend τ X')) b' (T' Θ τ X' x').

Lemma families_align_sym : forall Γ i B a ρ C R T Δ j B' a' ρ' C' R' T',
    families_align Γ i B a ρ C R T Δ j B' a' ρ' C' R' T' ->
    families_align Δ j B' a' ρ' C' R' T' Γ i B a ρ C R T.
Proof.
  intros Γ i B a ρ C R T Δ j B' a' ρ' C' R' T' HF Θ σ τ X Y x y c d Hσ Hτ HX HY Hc Hd.
  apply aligned_sym, (HF _ _ _ _ _ _ _ _ _ Hτ Hσ HY HX Hd Hc).
Qed.

Section FunctionAlignment.

Context (U : list universe_candidate) (HU : universe_invariants U).
Context (Γ Δ : ctx) (i j : nat) (A B A' B' : exp)
        (a a' : domain) (ρ ρ' : env) (C C' : exp).
Context (R R' : candidate) (T T' : ctx -> sub -> exp -> domain -> candidate).
Context (GA : glued_type U Γ i A a R) (GA' : glued_type U Δ j A' a' R').
Context (GB : wf_exp (A :: Γ) (a_typ i) B) (GB' : wf_exp (A' :: Δ) (a_typ j) B').
Context (Hdom : aligned Γ A a R Δ A' a' R').
Context (HF : families_align Γ i B a ρ C R T Δ j B' a' ρ' C' R' T').
Context (GT : forall Θ σ X x, weakening Θ Γ σ -> R Θ σ X x ->
    forall b, eval_exp C (extend_env ρ x) b ->
    glued_type U Θ i (a_sub B (a_extend σ X)) b (T Θ σ X x)).
Context (GT' : forall Θ σ X x, weakening Θ Δ σ -> R' Θ σ X x ->
    forall b, eval_exp C' (extend_env ρ' x) b ->
    glued_type U Θ j (a_sub B' (a_extend σ X)) b (T' Θ σ X x)).

Lemma function_alignment_action :
    let L := observed_candidate Γ (a_pi A B) (d_pi a ρ C) (callable R T Γ A B ρ C) in
    let L' := observed_candidate Δ (a_pi A' B') (d_pi a' ρ' C') (callable R' T' Δ A' B' ρ' C') in
    glued_type U Γ i (a_pi A B) (d_pi a ρ C) L ->
    glued_type U Δ j (a_pi A' B') (d_pi a' ρ' C') L' ->
    covariant_action Γ (a_pi A B) (d_pi a ρ C) L Δ (a_pi A' B') (d_pi a' ρ' C') L'.
Proof.
  cbn zeta; intros GP GP' Θ σ τ M N m n k V Hσ Hτ HM HN HME HNE HV Hmn Hm.
  destruct Hm as (_ & _ & Hquote & Hcall).
  assert (Hobs : wf_exp Θ (a_sub (a_pi A' B') τ) N /\ semantic_member (d_pi a' ρ' C') n /\
    term_under_weakening Θ (a_sub (a_pi A' B') τ) N (d_pi a' ρ' C') n).
  { eapply candidates_observed_related;
      [exact HU | exact GP | exact GP' | exact Hσ | exact Hτ | exact HV | exact Hmn | exact HN | exact HME | exact Hquote]. }
  destruct Hobs as (HNt & Hnm & HNq).
  split; [exact HNt |]. split; [exact Hnm |]. split; [exact HNq |].
  intros Ξ ω X x HW HK.
  pose proof (weakening_compose _ _ _ _ _ HW Hσ) as Hs.
  pose proof (weakening_compose _ _ _ _ _ HW Hτ) as Hs'.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HAw.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA') as HAw'.
  destruct (model_type_view _ _ _ _ HV) as (W & F & HArel & Hclose & Hcod & Heq).
  destruct (candidate_has_invariants _ _ _ _ _ _ GA' _ _ _ _ Hs' HK) as (HX' & (h & Q & HQ & Hq) & _).
  assert (Hxx : W x x).
  { exact (proj2 (at_type_coherent_r k h a a' a' W Q HArel HQ _ _) Hq). }
  assert (HX : wf_exp Ξ (a_sub A (a_compose σ ω)) X).
  {
    eapply type_gluing_move_term; [exact HU | exact GA' | exact GA | exact Hs' | exact Hs | exact (at_type_sym _ _ _ _ HArel) | exact HX'].
  }
  pose proof (proj2 (Hdom _ _ _ _ _ _ _ _ _ Hs Hs' HX HX'
             (reflexive_expression _ _ _ HX) (reflexive_expression _ _ _ HX') HArel Hxx) HK) as HK1.
  destruct (Hcall _ _ _ _ HW HK1) as (b & y & Hb & Hy & HyR).
  destruct (Hclose _ _ Hxx) as (b0 & b' & Hb0 & Hb').
  pose proof (exp_unique _ _ _ Hb0 _ Hb) as E; subst b0.
  destruct (proj2 (Heq _ _) Hmn _ _ Hxx) as (y0 & y' & Hy0 & Hy' & Hyy').
  pose proof (app_unique _ _ _ Hy0 _ Hy) as E; subst y0.
  pose proof (Hcod _ _ Hxx _ _ Hb Hb') as Hpair.
  pose proof (GT _ _ _ _ Hs HK1 _ Hb) as G1.
  pose proof (GT' _ _ _ _ Hs' HK _ Hb') as G2.
  destruct (canonical_binder_after_weakening _ _ _ _ _ _ _ _ _ _ a_pi
      HAw GB Hσ HW wf_pi wf_exp_eq_pi_sub HM HME) as (HAs & HBs & HMw & HEw).
  destruct (canonical_binder_after_weakening _ _ _ _ _ _ _ _ _ _ a_pi
      HAw' GB' Hτ HW wf_pi wf_exp_eq_pi_sub HN (reflexive_expression _ _ _ HN))
    as (HAs' & HBs' & HNw & _).
  destruct (at_lifted_instance _ _ _ _ _ _ _ _
      (weakening_is_typed _ _ _ Hs) HAw GB HX) as (HBx & Hnativel).
  destruct (at_lifted_instance _ _ _ _ _ _ _ _
      (weakening_is_typed _ _ _ Hs') HAw' GB' HX') as (HBx' & Hnativer).
  pose proof (convert_expression _ _ _ _ _
    (wf_app _ _ _ _ _ _ HAs HBs HMw HX) HBx Hnativel) as HMapp.
  pose proof (convert_expression _ _ _ _ _
    (wf_app _ _ _ _ _ _ HAs' HBs' HNw HX') HBx' Hnativer) as HNapp.
  pose proof (convert_equality _ _ _ _ _ _
    (wf_exp_eq_app_cong _ _ _ _ _ _ _ _ HAs HBs HEw (reflexive_expression _ _ _ HX))
    HBx Hnativel) as HAPP.
  destruct (preserve_at_id _ _ _ _ _ HBx HMapp HAPP) as (HMi & HAPPi).
  destruct (preserve_at_id _ _ _ _ _ HBx' HNapp (reflexive_expression _ _ _ HNapp)) as (HNi & _).
  pose proof (weakening_identity _ (expression_context _ _ _ HMapp)) as Hid.
  assert (HAPPi' : wf_exp_eq Ξ
    (a_sub (a_sub B' (a_extend (a_compose τ ω) X)) a_id)
    (a_app (a_sub M ω) X) (a_app (a_sub N ω) X)).
  { eapply type_gluing_move_eq; [exact HU | exact G1 | exact G2 | exact Hid | exact Hid | exact Hpair | exact HAPPi]. }
  exists b', y'; split; [exact Hb' |]. split; [exact Hy' |].
  apply (proj1 (HF _ _ _ _ _ _ _ _ _ Hs Hs' HK1 HK Hb Hb'
         _ _ _ _ _ _ _ _ _ Hid Hid HMi HNi HAPPi HAPPi' Hpair Hyy')), HyR.
Qed.
End FunctionAlignment.

Section PairAlignment.

Context (U : list universe_candidate) (HU : universe_invariants U).
Context (Γ Δ : ctx) (i j : nat) (A B A' B' : exp)
        (a a' : domain) (ρ ρ' : env) (C C' : exp).
Context (R R' : candidate) (T T' : ctx -> sub -> exp -> domain -> candidate).
Context (GA : glued_type U Γ i A a R) (GA' : glued_type U Δ j A' a' R').
Context (GB : wf_exp (A :: Γ) (a_typ i) B) (GB' : wf_exp (A' :: Δ) (a_typ j) B').
Context (Hdom : aligned Γ A a R Δ A' a' R').
Context (HF : families_align Γ i B a ρ C R T Δ j B' a' ρ' C' R' T').
Context (GT : forall Θ σ X x, weakening Θ Γ σ -> R Θ σ X x ->
    forall b, eval_exp C (extend_env ρ x) b ->
    glued_type U Θ i (a_sub B (a_extend σ X)) b (T Θ σ X x)).
Context (GT' : forall Θ σ X x, weakening Θ Δ σ -> R' Θ σ X x ->
    forall b, eval_exp C' (extend_env ρ' x) b ->
    glued_type U Θ j (a_sub B' (a_extend σ X)) b (T' Θ σ X x)).

Lemma pair_alignment_action :
    let L := observed_candidate Γ (a_sigma A B) (d_sigma a ρ C) (projectable R T Γ A B ρ C) in
    let L' := observed_candidate Δ (a_sigma A' B') (d_sigma a' ρ' C') (projectable R' T' Δ A' B' ρ' C') in
    glued_type U Γ i (a_sigma A B) (d_sigma a ρ C) L ->
    glued_type U Δ j (a_sigma A' B') (d_sigma a' ρ' C') L' ->
    covariant_action Γ (a_sigma A B) (d_sigma a ρ C) L Δ (a_sigma A' B') (d_sigma a' ρ' C') L'.
Proof.
  cbn zeta; intros GP GP' Θ σ τ M N m n k V Hσ Hτ HM HN HME HNE HV Hmn Hm.
  destruct Hm as (_ & _ & Hquote & Hproj).
  assert (Hobs : wf_exp Θ (a_sub (a_sigma A' B') τ) N /\ semantic_member (d_sigma a' ρ' C') n /\
    term_under_weakening Θ (a_sub (a_sigma A' B') τ) N (d_sigma a' ρ' C') n).
  { eapply candidates_observed_related;
      [exact HU | exact GP | exact GP' | exact Hσ | exact Hτ | exact HV | exact Hmn | exact HN | exact HME | exact Hquote]. }
  destruct Hobs as (HNt & Hnm & HNq).
  split; [exact HNt |]. split; [exact Hnm |]. split; [exact HNq |].
  intros Ξ ω HW.
  pose proof (weakening_compose _ _ _ _ _ HW Hσ) as Hs.
  pose proof (weakening_compose _ _ _ _ _ HW Hτ) as Hs'.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HAw.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA') as HAw'.
  destruct (model_type_view _ _ _ _ HV) as (W & F & HArel & Hclose & Hcod & Heq).
  destruct (Hproj _ _ HW) as (x & y & b & Hx & Hy & Hb & HX & HY).
  destruct (proj2 (Heq _ _) Hmn) as (v & x' & w & y' & Hv & Hx' & Hw & Hy' & Hxrel & Hyrel).
  pose proof (fst_unique _ _ _ Hv Hx) as E; subst v.
  pose proof (snd_unique _ _ Hw _ Hy) as E; subst w.
  destruct (Hclose _ _ Hxrel) as (b0 & b' & Hb0 & Hb').
  pose proof (exp_unique _ _ _ Hb0 _ Hb) as E; subst b0.
  pose proof (Hcod _ _ Hxrel _ _ Hb Hb') as Hpair.
  destruct (canonical_binder_after_weakening _ _ _ _ _ _ _ _ _ _ a_sigma
      HAw GB Hσ HW wf_sigma wf_exp_eq_sigma_sub HM HME) as (HAs & HBs & HMw & HEw).
  destruct (canonical_binder_after_weakening _ _ _ _ _ _ _ _ _ _ a_sigma
      HAw' GB' Hτ HW wf_sigma wf_exp_eq_sigma_sub HN (reflexive_expression _ _ _ HN))
    as (HAs' & HBs' & HNw & _).
  pose proof (wf_fst _ _ _ _ _ HAs HBs HMw) as HXwf.
  pose proof (wf_fst _ _ _ _ _ HAs' HBs' HNw) as HXwf'.
  pose proof (wf_exp_eq_fst_cong _ _ _ _ _ _ HAs HBs HEw) as Hfirst.
  assert (Hfirst' : wf_exp_eq Ξ (a_sub A' (a_compose τ ω))
      (a_fst (a_sub M ω)) (a_fst (a_sub N ω))).
  { eapply type_gluing_move_eq; [exact HU | exact GA | exact GA' | exact Hs | exact Hs' | exact HArel | exact Hfirst]. }
  pose proof (proj1 (Hdom _ _ _ _ _ _ _ _ _ Hs Hs' HXwf HXwf' Hfirst Hfirst' HArel Hxrel) HX) as HX'.
  pose proof (GT _ _ _ _ Hs HX _ Hb) as G1.
  pose proof (GT' _ _ _ _ Hs' HX' _ Hb') as G2.
  destruct (at_lifted_instance _ _ _ _ _ _ _ _
      (weakening_is_typed _ _ _ Hs) HAw GB HXwf) as (HBx & Hnativel).
  destruct (at_lifted_instance _ _ _ _ _ _ _ _
      (weakening_is_typed _ _ _ Hs') HAw' GB' HXwf') as (HBx' & Hnativer).
  pose proof (convert_expression _ _ _ _ _
    (wf_snd _ _ _ _ _ HAs HBs HMw) HBx Hnativel) as HMsnd.
  pose proof (convert_expression _ _ _ _ _
    (wf_snd _ _ _ _ _ HAs' HBs' HNw) HBx' Hnativer) as HNsnd.
  pose proof (convert_equality _ _ _ _ _ _
    (wf_exp_eq_snd_cong _ _ _ _ _ _ HAs HBs HEw) HBx Hnativel) as Hsecond.
  destruct (preserve_at_id _ _ _ _ _ HBx HMsnd Hsecond) as (HMi & Hsecondi).
  destruct (preserve_at_id _ _ _ _ _ HBx' HNsnd (reflexive_expression _ _ _ HNsnd)) as (HNi & _).
  pose proof (weakening_identity _ (expression_context _ _ _ HMsnd)) as Hid.
  assert (Hsecondi' : wf_exp_eq Ξ
    (a_sub (a_sub B' (a_extend (a_compose τ ω) (a_fst (a_sub N ω)))) a_id)
    (a_snd (a_sub M ω)) (a_snd (a_sub N ω))).
  { eapply type_gluing_move_eq; [exact HU | exact G1 | exact G2 | exact Hid | exact Hid | exact Hpair | exact Hsecondi]. }
  exists x', y', b'; split; [exact Hx' |]. split; [exact Hy' |].
  split; [exact Hb' |]. split; [exact HX' |].
  apply (proj1 (HF _ _ _ _ _ _ _ _ _ Hs Hs' HX HX' Hb Hb'
         _ _ _ _ _ _ _ _ _ Hid Hid HMi HNi Hsecondi Hsecondi' Hpair Hyrel)), HY.
Qed.
End PairAlignment.

Lemma quotes_agree_syntactically : forall U Γ Δ i j A B a b R T Θ σ τ k V M N m n,
    universe_invariants U ->
    glued_type U Γ i A a R -> glued_type U Δ j B b T ->
    weakening Θ Γ σ -> weakening Θ Δ τ -> at_type k a b V -> V m n ->
    quoted_term Θ (a_sub A σ) M a m -> quoted_term Θ (a_sub B τ) N b n ->
    wf_exp_eq Θ (a_sub B τ) M N.
Proof.
  intros U Γ Δ i j A B a b R T Θ σ τ k V M N m n HU HA HB Hσ Hτ Hk HV HM HN.
  destruct (quote_term_semantic_conversion _ _ _ _ _ _ _ _ _ Hk HV HM) as (W & HR & HME).
  destruct HN as (W' & HR' & HNE).
  pose proof (proj1 readback_unique _ _ _ HR _ HR') as E; subst W'.
  eapply wf_exp_eq_trans; [|exact (wf_exp_eq_sym _ _ _ _ HNE)].
  eapply type_gluing_move_eq; [exact HU | exact HA | exact HB | exact Hσ | exact Hτ | exact Hk | exact HME].
Qed.

Lemma related_neutral_observation : forall U Γ Δ i j A B a b R T Θ σ τ k V M N n n',
    universe_invariants U ->
    glued_type U Γ i A a R -> glued_type U Δ j B b T ->
    weakening Θ Γ σ -> weakening Θ Δ τ -> at_type k a b V ->
    wf_exp_eq Θ (a_sub A σ) M N ->
    ne_related n n' ->
    neutral_under_weakening Θ (a_sub A σ) M n ->
    neutral_under_weakening Θ (a_sub B τ) N n'.
Proof.
  intros U Γ Δ i j A B a b R T Θ σ τ k V M N n n' HU HA HB Hσ Hτ Hk HE Hrel HN.
  eapply compatible_neutral; [exact Hrel |].
  eapply convert_neutral_under_weakening.
  - eapply cumulative_type.
    + exact (substitute_type _ _ _ _ _ (weakening_is_typed _ _ _ Hτ) (glued_type_well_formed _ _ _ _ _ _ HB)).
    + apply Nat.le_max_r.
  - exact (type_gluing_syntax_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HU HA HB Hσ Hτ Hk).
  - exact (neutral_under_weakening_conversion _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ HE) HN).
Qed.

Section EqualityAlignment.

Context (U : list universe_candidate) (HU : universe_invariants U).
Context (Γ Δ : ctx) (i j : nat) (A X Y A' X' Y' : exp) (a x y a' x' y' : domain)
        (R R' : candidate).
Context (GA : glued_type U Γ i A a R) (GA' : glued_type U Δ j A' a' R').
Context (Hdom : aligned Γ A a R Δ A' a' R').
Context (HXR : forall Θ σ, weakening Θ Γ σ -> R Θ σ (a_sub X σ) x).
Context (HYR : forall Θ σ, weakening Θ Γ σ -> R Θ σ (a_sub Y σ) y).
Context (HXR' : forall Θ σ, weakening Θ Δ σ -> R' Θ σ (a_sub X' σ) x').
Context (HYR' : forall Θ σ, weakening Θ Δ σ -> R' Θ σ (a_sub Y' σ) y').
Context (HXT' : wf_exp Δ A' X') (HYT' : wf_exp Δ A' Y').

Lemma equality_alignment_action :
    let L := observed_candidate Γ (a_eq A X Y) (d_eq a x y) (reflexive_candidate R Γ A X Y a x y) in
    let L' := observed_candidate Δ (a_eq A' X' Y') (d_eq a' x' y') (reflexive_candidate R' Δ A' X' Y' a' x' y') in
    glued_type U Γ i (a_eq A X Y) (d_eq a x y) L ->
    glued_type U Δ j (a_eq A' X' Y') (d_eq a' x' y') L' ->
    covariant_action Γ (a_eq A X Y) (d_eq a x y) L Δ (a_eq A' X' Y') (d_eq a' x' y') L'.
Proof.
  cbn zeta; intros GE GE' Θ σ τ M N m n k V Hσ Hτ HM HN HME HNE HV Hmn Hm.
  destruct Hm as (_ & _ & Hquote & Hproof).
  assert (Hobs : wf_exp Θ (a_sub (a_eq A' X' Y') τ) N /\ semantic_member (d_eq a' x' y') n /\
    term_under_weakening Θ (a_sub (a_eq A' X' Y') τ) N (d_eq a' x' y') n).
  { eapply candidates_observed_related;
      [exact HU | exact GE | exact GE' | exact Hσ | exact Hτ | exact HV | exact Hmn | exact HN | exact HME | exact Hquote]. }
  destruct Hobs as (HNt & Hnm & HNq).
  split; [exact HNt |]. split; [exact Hnm |]. split; [exact HNq |].
  destruct (model_type_view _ _ _ _ HV) as (W & HAW & HX & HY & Heq).
  pose proof (proj2 (Heq _ _) Hmn) as Hpr.
  destruct Hproof as [(b & p & -> & Hp) | (Z & z & -> & HZR & HZX & HZY & HMR)].
  - left; inversion Hpr; subst.
    eexists _, _; split; [reflexivity |].
    eapply related_neutral_observation;
      [exact HU | exact GE | exact GE' | exact Hσ | exact Hτ | exact HV | exact HME | eassumption | exact Hp].
  - inversion Hpr as [v z' Hzz' Hzx' Hzy' Hxz' Hyz' EqZ EqN|]; subst.
    right.
    pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HAw.
    pose proof (glued_type_well_formed _ _ _ _ _ _ GA') as HAw'.
    destruct (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ Hσ HZR) as (HZwf & _ & _).
    assert (HZwf' : wf_exp Θ (a_sub A' τ) Z).
    { eapply type_gluing_move_term; [exact HU | exact GA | exact GA' | exact Hσ | exact Hτ | exact HAW | exact HZwf]. }
    pose proof (proj1 (Hdom _ _ _ _ _ _ _ _ _ Hσ Hτ HZwf HZwf'
      (reflexive_expression _ _ _ HZwf) (reflexive_expression _ _ _ HZwf') HAW Hzz') HZR) as HZR'.
    assert (Hendpt : forall L L' l l',
        R Θ σ (a_sub L σ) l -> R' Θ τ (a_sub L' τ) l' -> W l l' ->
        wf_exp_eq Θ (a_sub A' τ) (a_sub L σ) (a_sub L' τ)).
    {
      intros L L' l l' HR HR' HW.
      destruct (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ Hσ HR) as (HL & _ & HQl).
      destruct (candidate_has_invariants _ _ _ _ _ _ GA' _ _ _ _ Hτ HR') as (HL' & _ & HQl').
      eapply quotes_agree_syntactically; [exact HU | exact GA | exact GA' | exact Hσ | exact Hτ
        | exact HAW | exact HW | exact (observe_term _ _ _ _ _ HL HQl) | exact (observe_term _ _ _ _ _ HL' HQl')].
    }
    assert (HZeq : forall L L' l l',
       R Θ σ (a_sub L σ) l -> R' Θ τ (a_sub L' τ) l' -> W l l' ->
       wf_exp_eq Θ (a_sub A σ) Z (a_sub L σ) ->
       wf_exp_eq Θ (a_sub A' τ) Z (a_sub L' τ)).
    {
      intros L L' l l' HR HR' HW HE.
      eapply wf_exp_eq_trans; [| exact (Hendpt _ _ _ _ HR HR' HW)].
      eapply type_gluing_move_eq; [exact HU | exact GA | exact GA' | exact Hσ | exact Hτ | exact HAW | exact HE].
    }
    pose proof (HZeq _ _ _ _ (HXR _ _ Hσ) (HXR' _ _ Hτ) HX HZX) as HZX'.
    pose proof (HZeq _ _ _ _ (HYR _ _ Hσ) (HYR' _ _ Hτ) HY HZY) as HZY'.
    exists Z, z'; split; [reflexivity |]. split; [exact HZR' |].
    split; [exact HZX' |]. split; [exact HZY' |].
    eapply wf_exp_eq_trans; [exact (wf_exp_eq_sym _ _ _ _ HNE) |].
    eapply wf_exp_eq_trans.
    + eapply type_gluing_move_eq; [exact HU | exact GE | exact GE' | exact Hσ | exact Hτ | exact HV | exact HMR].
    + pose proof (type_gluing_syntax_equality _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HU GA GA' Hσ Hτ HAW) as HAe.
      pose proof (weakening_is_typed _ _ _ Hτ) as Hτt.
      pose proof (glued_type_well_formed _ _ _ _ _ _ GE') as HEqw.
      pose proof (substitute_type _ _ _ _ _ Hτt HEqw) as HEqwt.
      assert (Htarget : wf_exp_eq Θ (a_typ (Nat.max i j))
         (a_eq (a_sub A σ) Z Z) (a_sub (a_eq A' X' Y') τ)).
      {
        eapply wf_exp_eq_trans with (M' := a_eq (a_sub A' τ) (a_sub X' τ) (a_sub Y' τ)).
        - apply wf_exp_eq_eq_cong; [exact HAe | |];
            (eapply type_gluing_move_eq; [exact HU | exact GA' | exact GA | exact Hτ | exact Hσ
             | exact (at_type_sym _ _ _ _ HAW) | assumption]).
        - apply wf_exp_eq_sym; eapply cumulative_type_equality.
          + exact (expression_context _ _ _ HNt).
          + exact (wf_exp_eq_eq_sub _ _ _ _ _ _ _ Hτt HAw' HXT' HYT').
          + apply Nat.le_max_r.
      }
      eapply convert_equality.
      * eapply wf_exp_eq_refl_cong; [exact HAe | exact (reflexive_expression _ _ _ HZwf)].
      * exact (cumulative_type _ _ _ _ HEqwt (Nat.le_max_r i j)).
      * exact Htarget.
Qed.
End EqualityAlignment.

Definition universe_coherence (U : list universe_candidate) :=
  forall i P, nth_error U i = Some P ->
    forall Θ M N m n, P Θ M m -> wf_exp Θ (a_typ i) N ->
    wf_exp_eq Θ (a_typ i) M N ->
    type_rel (universes i) m n -> P Θ N n.

Lemma gluing_universes_coherent : forall k, universe_coherence (gluing_universes k).
Proof.
  induction k as [|k IH]; intros i P H; [destruct i; discriminate |].
  simpl in H.
  destruct (Nat.lt_ge_cases i (length (gluing_universes k))) as [Hlt | Hge].
  - apply (IH i P); now rewrite nth_error_app1 in H.
  - rewrite nth_error_app2 in H by exact Hge.
    assert (Hbound : i - length (gluing_universes k) < length (gluing_universe (gluing_universes k) :: nil)).
    { apply nth_error_Some; rewrite H; discriminate. }
    simpl in Hbound.
    assert (E : i - length (gluing_universes k) = 0) by lia.
    rewrite E in H; injection H as <-.
    assert (i = length (gluing_universes k)) by lia; subst i.
    intros Θ M N m n (R & HR) HN HE (S & HS).
    eexists.
    eapply glued_type_convert; [eapply glued_type_transport; [exact HR | exact HS] | exact HN | exact HE].
Qed.

Lemma natural_alignment_action : forall U Γ Δ,
    universe_invariants U -> wf_ctx Γ -> wf_ctx Δ ->
    let L := observed_candidate Γ a_nat d_nat
        (fun Θ σ M m => exists r, natural_realizes Θ M r /\ nat_rel r m) in
    let L' := observed_candidate Δ a_nat d_nat
        (fun Θ σ M m => exists r, natural_realizes Θ M r /\ nat_rel r m) in
    covariant_action Γ a_nat d_nat L Δ a_nat d_nat L'.
Proof.
  intros U Γ Δ HU HG HD; cbn zeta.
  intros Θ σ τ M N m n k V Hσ Hτ HM HN HME HNE HV Hmn (_ & _ & HQ & r & HR & Hrm).
  pose proof (glued_type_nat U Γ HG) as GN.
  pose proof (glued_type_nat U Δ HD) as GN'.
  assert (Hobs : wf_exp Θ (a_sub a_nat τ) N /\ semantic_member d_nat n /\ term_under_weakening Θ (a_sub a_nat τ) N d_nat n).
  { eapply candidates_observed_related; [exact HU | exact GN | exact GN' | exact Hσ | exact Hτ | exact HV | exact Hmn | exact HN | exact HME | exact HQ]. }
  destruct Hobs as (HNt & HNsem & HNq).
  split; [exact HNt |]. split; [exact HNsem |]. split; [exact HNq |].
  assert (Hnat : nat_rel m n) by exact (proj2 (model_type_view _ _ _ _ HV _ _) Hmn).
  exists r; split; [| exact (proj2 nat_rel_per _ _ _ Hrm Hnat)].
  pose proof (wf_nat Θ (expression_context _ _ _ HN)) as HNat.
  pose proof (wf_exp_eq_nat_sub _ _ _ (weakening_is_typed _ _ _ Hτ)) as HE.
  eapply realizes_conversion.
  - eapply convert_expression; [exact HN | exact HNat | exact HE].
  - eapply convert_equality; [exact (wf_exp_eq_sym _ _ _ _ HNE) | exact HNat | exact HE].
  - exact HR.
Qed.

Lemma universe_alignment_action : forall U Γ Δ i P,
    universe_invariants U -> universe_coherence U ->
    wf_ctx Γ -> wf_ctx Δ -> nth_error U i = Some P ->
    let L := observed_candidate Γ (a_typ i) (d_univ i) (fun Θ σ M m => P Θ M m) in
    let L' := observed_candidate Δ (a_typ i) (d_univ i) (fun Θ σ M m => P Θ M m) in
    covariant_action Γ (a_typ i) (d_univ i) L Δ (a_typ i) (d_univ i) L'.
Proof.
  intros U Γ Δ i P HU HC HG HD HP; cbn zeta.
  intros Θ σ τ M N m n k V Hσ Hτ HM HN HME HNE HV Hmn (_ & _ & HQ & Hval).
  pose proof (glued_type_univ U Γ i P HG HP) as GN.
  pose proof (glued_type_univ U Δ i P HD HP) as GN'.
  assert (Hobs : wf_exp Θ (a_sub (a_typ i) τ) N /\ semantic_member (d_univ i) n /\
    term_under_weakening Θ (a_sub (a_typ i) τ) N (d_univ i) n).
  { eapply candidates_observed_related; [exact HU | exact GN | exact GN' | exact Hσ | exact Hτ | exact HV | exact Hmn | exact HN | exact HME | exact HQ]. }
  destruct Hobs as (HNt & HNsem & HNq).
  split; [exact HNt |]. split; [exact HNsem |]. split; [exact HNq |].
  pose proof (wf_typ Θ i (expression_context _ _ _ HN)) as HTyp.
  pose proof (wf_exp_eq_typ_sub _ _ _ i (weakening_is_typed _ _ _ Hτ)) as Htype.
  refine (HC i P HP _ _ _ _ _ Hval _ _ _).
  - eapply convert_expression; [exact HN | exact HTyp | exact Htype].
  - eapply convert_equality; [exact HNE | exact HTyp | exact Htype].
  - destruct (model_type_view _ _ _ _ HV) as (_ & Q & Hlookup & Hq).
    assert (Hsmall : i < k).
    { rewrite <- universes_length; apply nth_error_Some; rewrite Hlookup; discriminate. }
    rewrite universes_lookup in Hlookup by exact Hsmall.
    injection Hlookup as <-; now apply Hq.
Qed.

Lemma neutral_alignment_action : forall U Γ Δ i j A A' a a' p p',
    universe_invariants U ->
    wf_exp Γ (a_typ i) A -> neutral_under_weakening Γ (a_typ i) A p ->
    wf_exp Δ (a_typ j) A' -> neutral_under_weakening Δ (a_typ j) A' p' ->
    let L := observed_candidate Γ A (d_neut a p) (neutral_candidate Γ A (fun m n => exists k, m = d_neut k n)) in
    let L' := observed_candidate Δ A' (d_neut a' p') (neutral_candidate Δ A' (fun m n => exists k, m = d_neut k n)) in
    covariant_action Γ A (d_neut a p) L Δ A' (d_neut a' p') L'.
Proof.
  intros U Γ Δ i j A A' a a' p p' HU HA HP HA' HP'; cbn zeta.
  intros Θ σ τ M N m n k V Hσ Hτ HM HN HME HNE HV Hmn (_ & _ & HQ & r & (c & ->) & HR).
  pose proof (glued_type_neutral U Γ i A a p HA HP) as GN.
  pose proof (glued_type_neutral U Δ j A' a' p' HA' HP') as GN'.
  assert (Hobs : wf_exp Θ (a_sub A' τ) N /\ semantic_member (d_neut a' p') n /\
    term_under_weakening Θ (a_sub A' τ) N (d_neut a' p') n).
  { eapply candidates_observed_related; [exact HU | exact GN | exact GN' | exact Hσ | exact Hτ | exact HV | exact Hmn | exact HN | exact HME | exact HQ]. }
  destruct Hobs as (HNt & HNsem & HNq).
  split; [exact HNt |]. split; [exact HNsem |]. split; [exact HNq |].
  destruct (model_type_view _ _ _ _ HV) as [_ HX].
  destruct (proj2 (HX _ _) Hmn) as (b & e & s & s' & Heq & -> & Hsp).
  inversion Heq; subst.
  exists s'; split; [exists e; reflexivity |].
  eapply related_neutral_observation;
    [exact HU | exact GN | exact GN' | exact Hσ | exact Hτ | exact HV | exact HME | exact Hsp | exact HR].
Qed.

Inductive glued_head (U : list universe_candidate) : ctx -> nat -> exp -> domain -> candidate -> Prop :=
| glued_head_nat : forall Γ, wf_ctx Γ ->
    glued_head U Γ 0 a_nat d_nat
      (observed_candidate Γ a_nat d_nat
        (fun Δ σ M m => exists r, natural_realizes Δ M r /\ nat_rel r m))
| glued_head_univ : forall Γ i P, wf_ctx Γ -> nth_error U i = Some P ->
    glued_head U Γ (S i) (a_typ i) (d_univ i)
      (observed_candidate Γ (a_typ i) (d_univ i) (fun Δ σ M m => P Δ M m))
| glued_head_neutral : forall Γ i A k n,
    wf_exp Γ (a_typ i) A ->
    neutral_under_weakening Γ (a_typ i) A n ->
    glued_head U Γ i A (d_neut k n)
      (observed_candidate Γ A (d_neut k n)
        (neutral_candidate Γ A (fun m n => exists k, m = d_neut k n)))
| glued_head_pi : forall Γ i A B a ρ C R T S,
    at_type i (d_pi a ρ C) (d_pi a ρ C) S ->
    glued_type U Γ i A a R ->
    wf_exp (A :: Γ) (a_typ i) B ->
    (forall Δ σ X x, weakening Δ Γ σ -> R Δ σ X x ->
       exists b, eval_exp C (extend_env ρ x) b) ->
    (forall Δ σ X x, weakening Δ Γ σ -> R Δ σ X x ->
       forall b, eval_exp C (extend_env ρ x) b ->
       glued_type U Δ i (a_sub B (a_extend σ X)) b (T Δ σ X x)) ->
    glued_head U Γ i (a_pi A B) (d_pi a ρ C)
      (observed_candidate Γ (a_pi A B) (d_pi a ρ C) (callable R T Γ A B ρ C))
| glued_head_sigma : forall Γ i A B a ρ C R T S,
    at_type i (d_sigma a ρ C) (d_sigma a ρ C) S ->
    glued_type U Γ i A a R ->
    wf_exp (A :: Γ) (a_typ i) B ->
    (forall Δ σ X x, weakening Δ Γ σ -> R Δ σ X x ->
       exists b, eval_exp C (extend_env ρ x) b) ->
    (forall Δ σ X x, weakening Δ Γ σ -> R Δ σ X x ->
       forall b, eval_exp C (extend_env ρ x) b ->
       glued_type U Δ i (a_sub B (a_extend σ X)) b (T Δ σ X x)) ->
    glued_head U Γ i (a_sigma A B) (d_sigma a ρ C)
      (observed_candidate Γ (a_sigma A B) (d_sigma a ρ C) (projectable R T Γ A B ρ C))
| glued_head_eq : forall Γ i A X Y a x y R S,
    at_type i (d_eq a x y) (d_eq a x y) S ->
    glued_type U Γ i A a R ->
    wf_exp Γ A X -> wf_exp Γ A Y ->
    (forall Δ σ, weakening Δ Γ σ -> R Δ σ (a_sub X σ) x) ->
    (forall Δ σ, weakening Δ Γ σ -> R Δ σ (a_sub Y σ) y) ->
    glued_head U Γ i (a_eq A X Y) (d_eq a x y)
      (observed_candidate Γ (a_eq A X Y) (d_eq a x y)
        (reflexive_candidate R Γ A X Y a x y)).

Lemma aligned_against_head : forall U Γ A a R,
    (forall Δ j B b T, glued_head U Δ j B b T -> aligned Γ A a R Δ B b T) ->
    forall Δ j B b T, glued_type U Δ j B b T -> aligned Γ A a R Δ B b T.
Proof.
  intros U Γ A a R Hhead Δ j B b T HT.
  induction HT;
    try solve [eapply Hhead; econstructor; eassumption].
  - eapply aligned_convert_right; [eapply glued_type_well_formed; eassumption | eassumption | eassumption].
  - eapply aligned_shift_right; [eapply glued_type_well_formed; eassumption | eassumption | eassumption].
  - eapply aligned_extensional_right; eassumption.
  - assumption.
  - eapply aligned_semantic_right; eassumption.
Qed.

Ltac reject_distinct_semantic_heads :=
  let H := fresh "Hsem" in
  intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? H;
  apply model_type_view in H; cbn [type_view] in H; contradiction.

Lemma glued_candidates_aligned : forall U,
    universe_invariants U -> universe_coherence U ->
    forall Γ i A a R, glued_type U Γ i A a R ->
    forall Δ j B b T, glued_type U Δ j B b T -> aligned Γ A a R Δ B b T.
Proof.
  intros U HU HC Γ i A a R H.
  induction H as
    [Γ HG
    |Γ i P HG HP
    |Γ i A k n HA HN
    |Γ i A B a ρ C R T S HS HA IHA HB HF HT IHT
    |Γ i A B a ρ C R T S HS HA IHA HB HF HT IHT
    |Γ i A X Y a x y R S HS HA IHA HX HY HRX HRY
    |Γ i A B a R HA IHA HB HE
    |Γ Γ' i A a R σ HA IHA Hσ
    |Γ i A a R K HA IHA HE
    |Γ i j A a R HA IHA Hle
    |Γ i A a b R S HA IHA HS].
  7-11: intros Δ j' B' b' T' HT'.
  7: apply aligned_sym; eapply aligned_convert_right;
       [exact (glued_type_well_formed _ _ _ _ _ _ HA) | exact HE | apply aligned_sym; exact (IHA _ _ _ _ _ HT')].
  7: apply aligned_sym; eapply aligned_shift_right;
       [exact (glued_type_well_formed _ _ _ _ _ _ HA) | exact Hσ | apply aligned_sym; exact (IHA _ _ _ _ _ HT')].
  7: apply aligned_sym; eapply aligned_extensional_right;
       [exact HE | apply aligned_sym; exact (IHA _ _ _ _ _ HT')].
  7: exact (IHA _ _ _ _ _ HT').
  7: apply aligned_sym; eapply aligned_semantic_right;
       [exact HS | apply aligned_sym; exact (IHA _ _ _ _ _ HT')].
  all: apply aligned_against_head; intros Δ j B' b T' Hright; destruct Hright as
    [Δ HD
    |Δ j P' HD HP'
    |Δ j D k' n' HD HDN
    |Δ j D E c τ F R' V S' HS' HD HE HF' HV
    |Δ j D E c τ F R' V S' HS' HD HE HF' HV
    |Δ j D X' Y' c x' y' R' S' HS' HD HX' HY' HRX' HRY'];
    try solve [reject_distinct_semantic_heads].
  - apply two_actions_align; eapply natural_alignment_action; eassumption.
  - intros Θ σ τ M N m n l V Hσ Hτ HM HNt HME HNE HV Hrel.
    destruct (model_type_view _ _ _ _ HV) as (E & _); subst j.
    rewrite HP in HP'; injection HP' as <-.
    apply (two_actions_align _ _ _ _ _ _ _ _
      (universe_alignment_action U Γ Δ i P HU HC HG HD HP)
      (universe_alignment_action U Δ Γ i P HU HC HD HG HP))
      with (k := l) (V := V); assumption.
  - apply two_actions_align; eapply neutral_alignment_action; eassumption.
  - assert (Hdom : aligned Γ A a R Δ D c R') by exact (IHA _ _ _ _ _ HD).
    assert (Hal : families_align Γ i B a ρ C R T Δ j E c τ F R' V).
    {
      intros Θ σ υ X Y x y b b' Hσ Hυ HX HY Hb Hb'.
      eapply IHT; [exact Hσ | exact HX | exact Hb |].
      exact (HV _ _ _ _ Hυ HY _ Hb').
    }
    pose proof (glued_type_pi _ _ _ _ _ _ _ _ _ _ _ HS HA HB HF HT) as GP.
    pose proof (glued_type_pi _ _ _ _ _ _ _ _ _ _ _ HS' HD HE HF' HV) as GP'.
    apply two_actions_align.
    + eapply function_alignment_action; eassumption.
    + eapply function_alignment_action; try eassumption.
      * now apply aligned_sym.
      * now apply families_align_sym.
  - assert (Hdom : aligned Γ A a R Δ D c R') by exact (IHA _ _ _ _ _ HD).
    assert (Hal : families_align Γ i B a ρ C R T Δ j E c τ F R' V).
    {
      intros Θ σ υ X Y x y b b' Hσ Hυ HX HY Hb Hb'.
      eapply IHT; [exact Hσ | exact HX | exact Hb |].
      exact (HV _ _ _ _ Hυ HY _ Hb').
    }
    pose proof (glued_type_sigma _ _ _ _ _ _ _ _ _ _ _ HS HA HB HF HT) as GP.
    pose proof (glued_type_sigma _ _ _ _ _ _ _ _ _ _ _ HS' HD HE HF' HV) as GP'.
    apply two_actions_align.
    + eapply pair_alignment_action; eassumption.
    + eapply pair_alignment_action; try eassumption.
      * now apply aligned_sym.
      * now apply families_align_sym.
  - assert (Hdom : aligned Γ A a R Δ D c R') by exact (IHA _ _ _ _ _ HD).
    pose proof (glued_type_eq _ _ _ _ _ _ _ _ _ _ _ HS HA HX HY HRX HRY) as GE.
    pose proof (glued_type_eq _ _ _ _ _ _ _ _ _ _ _ HS' HD HX' HY' HRX' HRY') as GE'.
    apply two_actions_align.
    + eapply equality_alignment_action; eassumption.
    + eapply equality_alignment_action; try eassumption; now apply aligned_sym.
Qed.

Lemma glued_type_change_universes : forall U Γ i A a R, glued_type U Γ i A a R ->
    forall V, (forall j, j < i -> nth_error U j = nth_error V j) ->
    glued_type V Γ i A a R.
Proof.
  intros U Γ i A a R H.
  induction H as
    [Γ HG
    |Γ i P HG HP
    |Γ i A k n HA HN
    |Γ i A B a ρ C R T S HS HA IHA HB HF HT IHT
    |Γ i A B a ρ C R T S HS HA IHA HB HF HT IHT
    |Γ i A X Y a x y R S HS HA IHA HX HY HRX HRY
    |Γ i A B a R HA IHA HB HE
    |Γ Γ' i A a R σ HA IHA Hσ
    |Γ i A a R K HA IHA HE
    |Γ i j A a R HA IHA Hle
    |Γ i A a b R S HA IHA HS]; intros V HV.
  - now apply glued_type_nat.
  - apply glued_type_univ; [exact HG | rewrite <- HV by lia; exact HP].
  - now apply glued_type_neutral.
  - eapply glued_type_pi; [exact HS | exact (IHA V HV) | exact HB | exact HF |].
    intros; eapply IHT; eassumption.
  - eapply glued_type_sigma; [exact HS | exact (IHA V HV) | exact HB | exact HF |].
    intros; eapply IHT; eassumption.
  - eapply glued_type_eq; [exact HS | exact (IHA V HV) | exact HX | exact HY | exact HRX | exact HRY].
  - eapply glued_type_convert; [exact (IHA V HV) | exact HB | exact HE].
  - exact (glued_type_shift V _ _ _ _ _ _ _ (IHA V HV) Hσ).
  - eapply glued_type_extensional; [exact (IHA V HV) | exact HE].
  - eapply glued_type_cumulative; [apply IHA; intros; apply HV; lia | exact Hle].
  - eapply glued_type_transport; [exact (IHA V HV) | exact HS].
Qed.

Lemma gluing_universes_lookup : forall n i, i < n ->
    nth_error (gluing_universes n) i = Some (gluing_universe (gluing_universes i)).
Proof.
  induction n as [|n IH]; intros i H; [lia|].
  simpl.
  destruct (Nat.lt_ge_cases i n) as [Hlt | Hge].
  - rewrite nth_error_app1 by (rewrite gluing_universes_length; exact Hlt).
    exact (IH _ Hlt).
  - assert (i = n) by lia; subst i.
    rewrite nth_error_app2 by (rewrite gluing_universes_length; lia).
    now rewrite gluing_universes_length, Nat.sub_diag.
Qed.

Lemma glued_type_at_prefix : forall n k Γ i A a R,
    i <= n -> i <= k -> glued_type (gluing_universes n) Γ i A a R ->
    glued_type (gluing_universes k) Γ i A a R.
Proof.
  intros n k Γ i A a R Hn Hk H.
  eapply glued_type_change_universes; [exact H |].
  intros j Hj; rewrite !gluing_universes_lookup by lia; reflexivity.
Qed.

Definition glued_term U Γ A M a m :=
  exists i R, glued_type U Γ i A a R /\ R Γ a_id M m.

Lemma glued_term_typing : forall U Γ A M a m,
    glued_term U Γ A M a m -> wf_exp Γ A M.
Proof.
  intros U Γ A M a m (i & R & HA & HM).
  pose proof (glued_type_well_formed _ _ _ _ _ _ HA) as HT.
  pose proof (weakening_identity _ (expression_context _ _ _ HT)) as Hid.
  destruct (candidate_has_invariants _ _ _ _ _ _ HA _ _ _ _ Hid HM) as (HMi & _ & _).
  exact (convert_expression _ _ _ _ _ HMi HT (type_substitution_identity _ _ _ HT)).
Qed.

Lemma glued_term_quote : forall U Γ A M a m,
    glued_term U Γ A M a m -> quoted_term Γ A M a m.
Proof.
  intros U Γ A M a m (i & R & HA & HM).
  pose proof (glued_type_well_formed _ _ _ _ _ _ HA) as HT.
  pose proof (weakening_identity _ (expression_context _ _ _ HT)) as Hid.
  destruct (candidate_has_invariants _ _ _ _ _ _ HA _ _ _ _ Hid HM) as (HMi & _ & HQ).
  eapply quote_term_type_conversion; [exact HT | exact (type_substitution_identity _ _ _ HT) |].
  exact (observe_term _ _ _ _ _ HMi HQ).
Qed.

Lemma glued_readback_soundness : forall U Γ A M ρ a m,
    initial_env Γ ρ ->
    eval_exp A ρ a ->
    eval_exp M ρ m ->
    glued_term U Γ A M a m ->
    exists W, nbe Γ M A W /\ wf_exp_eq Γ A M W.
Proof.
  intros U Γ A M ρ a m Hρ HA HM HG.
  destruct (glued_term_quote _ _ _ _ _ _ HG) as (W & HR & HE).
  exists W; split; [eapply nbe_run; eassumption | exact HE].
Qed.

Lemma glued_term_change : forall U Γ A B M N a b m n k j V,
    universe_invariants U -> universe_coherence U ->
    glued_term U Γ A M a m ->
    wf_exp Γ (a_typ j) B -> wf_exp_eq Γ (a_typ j) A B ->
    wf_exp Γ B N -> wf_exp_eq Γ B M N ->
    at_type k a b V -> V m n ->
    glued_term U Γ B N b n.
Proof.
  intros U Γ A B M N a b m n k j V HU HC
    (i & R & HA & HM) HB HAB HN HME Hk HV.
  set (l := Nat.max k (Nat.max i j)).
  pose proof (cumulative_type _ _ _ l HB ltac:(unfold l; lia)) as HBl.
  pose proof (expression_context _ _ _ HB) as HΓ.
  pose proof (cumulative_type_equality _ _ _ _ l HΓ HAB ltac:(unfold l; lia)) as HABl.
  pose proof (glued_type_cumulative _ _ _ l _ _ _ HA ltac:(unfold l; lia)) as HAl.
  pose proof (glued_type_convert _ _ _ _ _ _ _ HAl HBl HABl) as HGB.
  pose proof (model_type_lift _ _ _ _ _ (Nat.le_max_l k (Nat.max i j)) Hk) as Hkl.
  pose proof (glued_type_transport _ _ _ _ _ _ _ _ HGB Hkl) as HGB'.
  exists l, (fun Θ σ P p => exists r, R Θ σ P r /\ V r p); split; [exact HGB' |].
  assert (HMw : wf_exp Γ A M) by exact (glued_term_typing _ _ _ _ _ _ (ex_intro _ i (ex_intro _ R (conj HA HM)))).
  pose proof (glued_type_well_formed _ _ _ _ _ _ HA) as HAw.
  pose proof (weakening_identity _ HΓ) as Hid.
  assert (HMEa : wf_exp_eq Γ A M N).
  { eapply (convert_equality _ _ _ l); [exact HME | exact (cumulative_type _ _ _ l HAw ltac:(unfold l; lia))
                                    | exact (wf_exp_eq_sym _ _ _ _ HABl)]. }
  destruct (preserve_at_id _ _ _ _ _ HAw HMw HMEa) as (HMi & HMEi).
  destruct (preserve_at_id _ _ _ _ _ HB HN (wf_exp_eq_sym _ _ _ _ HME)) as (HNi & HNEi).
  apply (proj1 (glued_candidates_aligned _ HU HC _ _ _ _ _ HA _ _ _ _ _ HGB'
         _ _ _ _ _ _ _ _ _ Hid Hid HMi HNi HMEi (wf_exp_eq_sym _ _ _ _ HNEi) Hk HV)), HM.
Qed.

Lemma glued_term_expression_change : forall U Γ A M N a m,
    universe_invariants U -> universe_coherence U ->
    glued_term U Γ A M a m ->
    wf_exp Γ A N -> wf_exp_eq Γ A M N ->
    glued_term U Γ A N a m.
Proof.
  intros U Γ A M N a m HU HC (i & R & HA & HM) HN HE.
  exists i, R; split; [exact HA |].
  pose proof (glued_type_well_formed _ _ _ _ _ _ HA) as HAw.
  pose proof (weakening_identity _ (expression_context _ _ _ HAw)) as Hid.
  destruct (candidate_has_invariants _ _ _ _ _ _ HA _ _ _ _ Hid HM) as (HMi & (k & V & HV & Hrel) & _).
  destruct (preserve_at_id _ _ _ _ _ HAw HN (wf_exp_eq_sym _ _ _ _ HE)) as (HNi & HEi).
  apply (proj1 (glued_candidates_aligned _ HU HC _ _ _ _ _ HA _ _ _ _ _ HA
         _ _ _ _ _ _ _ _ _ Hid Hid HMi HNi (wf_exp_eq_sym _ _ _ _ HEi) (wf_exp_eq_sym _ _ _ _ HEi) HV Hrel)), HM.
Qed.

Lemma glued_term_type_change : forall U Γ A B M a m j,
    glued_term U Γ A M a m -> wf_exp Γ (a_typ j) B -> wf_exp_eq Γ (a_typ j) A B ->
    glued_term U Γ B M a m.
Proof.
  intros U Γ A B M a m j (i & R & HA & HM) HB HE.
  pose proof (expression_context _ _ _ HB) as HΓ.
  exists (Nat.max i j), R; split; [|exact HM].
  eapply glued_type_convert.
  - eapply glued_type_cumulative; [exact HA | apply Nat.le_max_l].
  - eapply cumulative_type; [exact HB | apply Nat.le_max_r].
  - eapply cumulative_type_equality; [exact HΓ | exact HE | apply Nat.le_max_r].
Qed.

Inductive glued_environment (U : list universe_candidate) (Θ : ctx) : ctx -> sub -> env -> Prop :=
| glued_environment_empty : forall σ ρ,
    wf_sub Θ nil σ -> glued_environment U Θ nil σ ρ
| glued_environment_cons : forall Γ A i σ ρ a,
    wf_sub Θ (A :: Γ) σ ->
    wf_exp Γ (a_typ i) A ->
    glued_environment U Θ Γ (a_compose a_weaken σ) (drop_env ρ) ->
    eval_exp A (drop_env ρ) a ->
    glued_term U Θ (a_sub A (a_compose a_weaken σ)) (a_sub (a_var 0) σ) a (ρ 0) ->
    ρ = extend_env (drop_env ρ) (ρ 0) ->
    glued_environment U Θ (A :: Γ) σ ρ.

Lemma glued_environment_typing : forall U Θ Γ σ ρ,
    glued_environment U Θ Γ σ ρ -> wf_sub Θ Γ σ.
Proof. intros U Θ Γ σ ρ H; destruct H; assumption. Qed.

Lemma glued_environment_semantic : forall U Θ Γ σ ρ,
    glued_environment U Θ Γ σ ρ -> env_related Γ ρ ρ.
Proof.
  intros U Θ Γ σ ρ HE; induction HE; simpl; [exact I |].
  destruct H2 as (j & R & HA & HM).
  pose proof (glued_type_well_formed _ _ _ _ _ _ HA) as HT.
  destruct (candidate_has_invariants _ _ _ _ _ _ HA _ _ _ _ (weakening_identity _ (expression_context _ _ _ HT)) HM)
    as (_ & (k & V & HV & Hr) & _).
  split; [exact IHHE |].
  exists a, a, V; repeat split; try assumption.
  now exists k.
Qed.

Lemma glued_environment_conversion : forall U Θ Γ σ τ ρ,
    universe_invariants U -> universe_coherence U ->
    glued_environment U Θ Γ σ ρ ->
    wf_sub Θ Γ τ -> wf_sub_eq Θ Γ σ τ ->
    glued_environment U Θ Γ τ ρ.
Proof.
  intros U Θ Γ σ τ ρ HU HC HE; revert τ.
  induction HE as [σ ρ HS|Γ A i σ ρ a HS HA E IH Hv HM Hcan]; intros τ HT Hσeq.
  - now apply glued_environment_empty.
  - pose proof (proj2 (substitution_contexts _ _ _ HT)) as HG.
    pose proof (wf_sub_weaken _ _ HG) as HW.
    pose proof (wf_sub_compose _ _ _ _ _ HS HW) as Hwl.
    pose proof (wf_sub_compose _ _ _ _ _ HT HW) as Hwr.
    assert (HWE : wf_sub_eq Θ Γ (a_compose a_weaken σ) (a_compose a_weaken τ)).
    { eapply wf_sub_eq_compose_cong; [exact Hσeq | now apply reflexive_substitution]. }
    pose proof (substitute_type _ _ _ _ _ Hwr HA) as Hright.
    assert (HEq : wf_exp_eq Θ (a_typ i) (a_sub A (a_compose a_weaken σ)) (a_sub A (a_compose a_weaken τ))).
    { eapply substitute_type_equality; [exact Hwl | exact HWE | now apply reflexive_expression]. }
    assert (Hvar : wf_exp Θ (a_sub A (a_compose a_weaken τ)) (a_sub (a_var 0) τ)).
    {
      eapply convert_expression; [eapply wf_exp_sub; [exact HT | now apply type_of_first_variable] | exact Hright |].
      apply wf_exp_eq_sym; eapply type_substitution_compose; eassumption.
    }
    assert (Hterm : wf_exp_eq Θ (a_sub A (a_compose a_weaken τ)) (a_sub (a_var 0) σ) (a_sub (a_var 0) τ)).
    {
      eapply convert_equality; [|exact Hright|].
      - eapply wf_exp_eq_sub_cong; [apply wf_exp_eq_var; [exact HG | apply here] |exact Hσeq].
      - eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; eapply type_substitution_compose; eassumption | exact HEq].
    }
    eapply glued_environment_cons.
    + exact HT.
    + exact HA.
    + exact (IH (a_compose a_weaken τ) Hwr HWE).
    + exact Hv.
    + eapply glued_term_expression_change;
        [exact HU | exact HC | exact (glued_term_type_change _ _ _ _ _ _ _ _ HM Hright HEq) | exact Hvar | exact Hterm].
    + exact Hcan.
Qed.

Lemma glued_environment_extend : forall U Θ Γ σ ρ A a m M i,
    universe_invariants U -> universe_coherence U ->
    glued_environment U Θ Γ σ ρ ->
    wf_exp Γ (a_typ i) A ->
    eval_exp A ρ a ->
    glued_term U Θ (a_sub A σ) M a m ->
    glued_environment U Θ (A :: Γ) (a_extend σ M) (extend_env ρ m).
Proof.
  intros U Θ Γ σ ρ A a m M i HU HC HEnv HA HE HM.
  pose proof (glued_environment_typing _ _ _ _ _ HEnv) as HS.
  pose proof (glued_term_typing _ _ _ _ _ _ HM) as HMw.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HMw) as Hext.
  pose proof (proj2 (substitution_contexts _ _ _ Hext)) as HG.
  pose proof (wf_sub_weaken _ _ HG) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ Hext HW) as HT.
  pose proof (wf_sub_eq_p_extend _ _ _ _ _ _ HS HA HMw) as Hp.
  assert (HEq : wf_exp_eq Θ (a_typ i) (a_sub A (a_compose a_weaken (a_extend σ M))) (a_sub A σ)).
  { eapply substitute_type_equality; [exact HT | exact Hp | now apply reflexive_expression]. }
  pose proof (substitute_type _ _ _ _ _ HT HA) as Hd.
  assert (Hexpr : wf_exp Θ (a_sub A (a_compose a_weaken (a_extend σ M))) (a_sub (a_var 0) (a_extend σ M))).
  {
    eapply convert_expression; [eapply wf_exp_sub; [exact Hext | now apply type_of_first_variable] | exact Hd |].
    apply wf_exp_eq_sym; eapply type_substitution_compose; eassumption.
  }
  eapply glued_environment_cons.
  - exact Hext.
  - exact HA.
  - eapply glued_environment_conversion; [exact HU | exact HC | exact HEnv | exact HT | now apply wf_sub_eq_sym].
  - exact HE.
  - eapply glued_term_type_change; [|exact Hd|exact (wf_exp_eq_sym _ _ _ _ HEq)].
    eapply glued_term_expression_change; [exact HU | exact HC | exact HM | |].
    + eapply convert_expression; [exact Hexpr | exact (substitute_type _ _ _ _ _ HS HA) | exact HEq].
    + apply wf_exp_eq_sym; exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ HS HA HMw).
  - reflexivity.
Qed.

Lemma glued_environment_lookup : forall U Θ Γ σ ρ x A,
    universe_invariants U -> universe_coherence U ->
    glued_environment U Θ Γ σ ρ -> ctx_lookup x A Γ ->
    exists a, eval_exp A ρ a /\ glued_term U Θ (a_sub A σ) (a_sub (a_var x) σ) a (ρ x).
Proof.
  intros U Θ Γ σ ρ x A HU HC HE HL; revert σ ρ HE.
  induction HL as [A Γ | x A Γ B HL IH]; intros σ ρ HE.
  - inversion HE as [| Γ' A' i σ' ρ' a HS HA Htail Hv HM Hcan]; subst.
    pose proof (proj2 (substitution_contexts _ _ _ HS)) as HG.
    pose proof (wf_sub_weaken _ _ HG) as HW.
    exists a; split.
    + eapply eval_exp_sub; [apply eval_sub_weaken | exact Hv].
    + eapply glued_term_type_change; [exact HM | | eapply type_substitution_compose; eassumption].
      eapply substitute_type; [exact HS | eapply substitute_type; eassumption].
  - inversion HE as [| Γ' B' i σ' ρ' ba HS HB Htail Hv HM Hcan]; subst.
    destruct (IH _ _ Htail) as (a & Ha & Hx).
    pose proof (proj2 (substitution_contexts _ _ _ HS)) as HG.
    pose proof (wf_sub_weaken _ _ HG) as HW.
    pose proof (proj2 (substitution_contexts _ _ _ HW)) as HG'.
    pose proof (wf_vlookup _ _ _ HG' HL) as HX.
    destruct (variable_type _ _ _ HG' HL) as (j & HAt).
    pose proof (substitute_type _ _ _ _ _ HS (substitute_type _ _ _ _ _ HW HAt)) as HAw.
    pose proof (type_substitution_compose _ _ _ _ _ _ _ HS HW HAt) as Hcomp.
    exists a; split.
    + eapply eval_exp_sub; [apply eval_sub_weaken | exact Ha].
    + eapply glued_term_expression_change;
        [exact HU | exact HC | exact (glued_term_type_change _ _ _ _ _ _ _ _ Hx HAw Hcomp) | |].
      * exact (wf_exp_sub _ _ _ _ _ HS (wf_vlookup _ _ _ HG (there _ _ _ _ HL))).
      * eapply wf_exp_eq_trans.
        -- eapply convert_equality; [eapply wf_exp_eq_sub_compose; eassumption | exact HAw | exact Hcomp].
        -- eapply wf_exp_eq_sub_cong.
           ++ exact (wf_exp_eq_var_weaken _ _ _ _ HG HL).
           ++ now apply reflexive_substitution.
Qed.


Lemma natural_glued_term : forall U Θ M r m, natural_realizes Θ M r -> nat_rel r m ->
    glued_term U Θ a_nat M d_nat m.
Proof.
  intros U Θ M r m HR Hsem.
  pose proof (natural_realizes_typing _ _ _ HR) as HM.
  pose proof (expression_context _ _ _ HM) as HΘ.
  pose proof (wf_nat _ HΘ) as HNat.
  destruct (preserve_at_id _ _ _ _ _ HNat HM (reflexive_expression _ _ _ HM)) as (HMi & _).
  eexists 0, _; split; [exact (glued_type_nat U _ HΘ) |].
  split; [exact HMi |]. split.
  - exists 0, nat_rel; split; [apply model_nat | exact (per_right _ nat_rel_per _ _ Hsem)].
  - split; [|exists r; tauto].
    intros Ξ τ Hτ.
    pose proof (weakening_is_typed _ _ _ Hτ) as HS.
    pose proof (wf_sub_id _ HΘ) as HI.
    pose proof (wf_sub_compose _ _ _ _ _ HS HI) as HC.
    pose proof (substitute_type _ _ _ _ _ HS (substitute_type _ _ _ _ _ HI HNat)) as Htyped.
    assert (HE : wf_exp_eq Ξ (a_typ 0) a_nat (a_sub (a_sub a_nat a_id) τ)).
    {
      apply wf_exp_eq_sym.
      eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HS HI HNat) |].
      exact (wf_exp_eq_nat_sub _ _ _ HC).
    }
    eapply quote_term_type_conversion; [exact Htyped | exact HE |].
    eapply quote_term_semantic_conversion; [exact (model_nat (universes 0)) | exact Hsem |].
    apply natural_realizes_quote; exact (natural_realizes_weaken _ _ _ HR _ _ Hτ).
Qed.

Lemma glued_term_as_natural : forall U Θ M m,
    universe_invariants U -> universe_coherence U ->
    glued_term U Θ a_nat M d_nat m ->
    exists r, natural_realizes Θ M r /\ nat_rel r m.
Proof.
  intros U Θ M m HU HC (i & R & HA & HR).
  pose proof (glued_type_well_formed _ _ _ _ _ _ HA) as HAt.
  pose proof (expression_context _ _ _ HAt) as HΘ.
  pose proof (weakening_identity _ HΘ) as Hid.
  destruct (candidate_has_invariants _ _ _ _ _ _ HA _ _ _ _ Hid HR) as (HM & (k & V & HV & Hrel) & HQ).
  pose proof (glued_type_nat U _ HΘ) as GN.
  pose proof (model_nat (universes 0)) as Hnat.
  assert (Hnrel : nat_rel m m).
  { exact (proj1 (at_type_coherent_l _ 0 _ _ _ _ _ HV Hnat _ _) Hrel). }
  pose proof (reflexive_expression _ _ _ HM) as Hexp.
  pose proof (proj1 (glued_candidates_aligned _ HU HC _ _ _ _ _ HA _ _ _ _ _ GN
    _ _ _ _ _ _ _ _ _ Hid Hid HM HM Hexp Hexp Hnat Hnrel) HR) as (_ & _ & _ & r & Hr & Hm).
  exists r; tauto.
Qed.

Lemma type_gluing_as_term : forall k Θ i M m R,
    i < k -> glued_type (gluing_universes k) Θ i M m R ->
    glued_term (gluing_universes k) Θ (a_typ i) M (d_univ i) m.
Proof.
  intros k Θ i M m R Hlt HG.
  pose proof (glued_type_well_formed _ _ _ _ _ _ HG) as HM.
  pose proof (expression_context _ _ _ HM) as HΘ.
  pose proof (wf_typ Θ i HΘ) as HTyp.
  destruct (preserve_at_id _ _ _ _ _ HTyp HM (reflexive_expression _ _ _ HM)) as (HMi & _).
  pose proof (gluing_universes_lookup _ _ Hlt) as Hlookup.
  eexists (S i), _; split; [exact (glued_type_univ _ _ _ _ HΘ Hlookup) |].
  split; [exact HMi |]. split.
  - exists (S i), (type_rel (universes i)); split; [apply typed_universe_value |].
    exact (glued_type_semantic _ _ _ _ _ _ HG).
  - split.
    + intros Ξ τ Hτ.
      pose proof (weakening_is_typed _ _ _ Hτ) as HS.
      pose proof (wf_sub_id _ HΘ) as HI.
      pose proof (wf_sub_compose _ _ _ _ _ HS HI) as HC.
      pose proof (substitute_type _ _ _ _ _ HS (substitute_type _ _ _ _ _ HI HTyp)) as Htyped.
      assert (HE : wf_exp_eq Ξ (a_typ (S i)) (a_typ i) (a_sub (a_sub (a_typ i) a_id) τ)).
      {
        apply wf_exp_eq_sym.
        eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HS HI HTyp) |].
        exact (wf_exp_eq_typ_sub _ _ _ _ HC).
      }
      eapply quote_term_type_conversion; [exact Htyped | exact HE |].
      apply quote_term_universe.
      exact (quotation_of_type _ _ _ _ (proj1 (quoted_candidate_reflects _ _ _ _ _ _
         (gluing_universes_quote k) HG)) _ _ Hτ).
    + exists R.
      change (glued_type (gluing_universes i) Θ (length (gluing_universes i)) M m R).
      rewrite gluing_universes_length.
      eapply (glued_type_at_prefix k i); [lia | reflexivity | exact HG].
Qed.

Definition typing_respects_gluing U Γ A M :=
  forall Θ σ ρ, glued_environment U Θ Γ σ ρ ->
    exists a m, eval_exp A ρ a /\ eval_exp M ρ m /\ glued_term U Θ (a_sub A σ) (a_sub M σ) a m.

Definition substitution_respects_gluing U Γ Δ τ :=
  forall Θ σ ρ, glued_environment U Θ Γ σ ρ ->
    exists θ, eval_sub τ ρ θ /\ glued_environment U Θ Δ (a_compose τ σ) θ.

Lemma gluing_var : forall U Γ A x,
    universe_invariants U -> universe_coherence U ->
    ctx_lookup x A Γ -> typing_respects_gluing U Γ A (a_var x).
Proof.
  intros U Γ A x HU HC HL Θ σ ρ HE.
  destruct (glued_environment_lookup _ _ _ _ _ _ _ HU HC HE HL) as (a & HA & HM).
  exists a, (ρ x); split; [exact HA | split; [constructor | exact HM]].
Qed.

Lemma gluing_sub_id : forall U Γ, universe_invariants U -> universe_coherence U ->
    substitution_respects_gluing U Γ Γ a_id.
Proof.
  intros U Γ HU HC Θ σ ρ HE; exists ρ; split; [constructor |].
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (wf_sub_id _ (proj2 (substitution_contexts _ _ _ HS))) as HI.
  eapply glued_environment_conversion;
    [exact HU | exact HC | exact HE | exact (wf_sub_compose _ _ _ _ _ HS HI) |].
  apply wf_sub_eq_sym; now apply wf_sub_eq_id_compose_right.
Qed.

Lemma gluing_sub_weaken : forall U Γ A, substitution_respects_gluing U (A :: Γ) Γ a_weaken.
Proof.
  intros U Γ A Θ σ ρ HE; inversion HE; subst.
  exists (drop_env ρ); split; [constructor | assumption].
Qed.

Lemma gluing_sub_compose : forall U Γ Δ Ξ σ τ,
    universe_invariants U -> universe_coherence U ->
    wf_sub Γ Δ τ -> wf_sub Δ Ξ σ ->
    substitution_respects_gluing U Γ Δ τ ->
    substitution_respects_gluing U Δ Ξ σ ->
    substitution_respects_gluing U Γ Ξ (a_compose σ τ).
Proof.
  intros U Γ Δ Ξ σ τ HU HC HT HS Hτ Hσ Θ δ ρ HE.
  destruct (Hτ _ _ _ HE) as (θ & Hθ & HTglue).
  destruct (Hσ _ _ _ HTglue) as (η & Hη & HSglue).
  exists η; split; [eapply eval_sub_compose; eassumption |].
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HD.
  eapply glued_environment_conversion;
    [exact HU | exact HC | exact HSglue | eapply wf_sub_compose; [exact HD | eapply wf_sub_compose; eassumption] |].
  apply wf_sub_eq_sym; eapply wf_sub_eq_compose_assoc; eassumption.
Qed.

Lemma gluing_sub_extend : forall U Γ Δ τ A M i,
    universe_invariants U -> universe_coherence U ->
    wf_sub Γ Δ τ -> wf_exp Δ (a_typ i) A -> wf_exp Γ (a_sub A τ) M ->
    substitution_respects_gluing U Γ Δ τ ->
    typing_respects_gluing U Γ (a_sub A τ) M ->
    substitution_respects_gluing U Γ (A :: Δ) (a_extend τ M).
Proof.
  intros U Γ Δ τ A M i HU HC HT HA HM Hτ Hterm Θ σ ρ HE.
  destruct (Hτ _ _ _ HE) as (θ & Hθ & Hglue).
  destruct (Hterm _ _ _ HE) as (a & m & HAe & HMe & HG).
  inversion HAe; subst; resolve_eval.
  pose proof (glued_environment_typing _ _ _ _ _ Hglue) as HTS.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (substitute_type _ _ _ _ _ HTS HA) as HCtype.
  pose proof (type_substitution_compose _ _ _ _ _ _ _ HS HT HA) as HEtype.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ HG HCtype (wf_exp_eq_sym _ _ _ _ HEtype)) as HG'.
  assert (Hextended : glued_environment U Θ (A :: Δ)
      (a_extend (a_compose τ σ) (a_sub M σ)) (extend_env θ m)).
  { eapply glued_environment_extend; [exact HU | exact HC | exact Hglue | exact HA | eassumption | exact HG']. }
  exists (extend_env θ m); split; [eapply eval_sub_extend; eassumption |].
  eapply glued_environment_conversion;
    [exact HU | exact HC | exact Hextended | eapply wf_sub_compose; [exact HS | eapply wf_sub_extend; eassumption] |].
  apply wf_sub_eq_sym; eapply wf_sub_eq_extend_compose; eassumption.
Qed.

Lemma gluing_exp_sub : forall U Γ Δ τ A M,
    universe_invariants U -> universe_coherence U ->
    wf_sub Γ Δ τ -> wf_exp Δ A M ->
    substitution_respects_gluing U Γ Δ τ ->
    typing_respects_gluing U Δ A M ->
    typing_respects_gluing U Γ (a_sub A τ) (a_sub M τ).
Proof.
  intros U Γ Δ τ A M HU HC HT HM Hτ Hterm Θ σ ρ HE.
  destruct (Hτ _ _ _ HE) as (θ & Hθ & Hglue).
  destruct (Hterm _ _ _ Hglue) as (a & m & HAe & HMe & HG).
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  destruct (expression_type _ _ _ HM) as (i & HA).
  pose proof (substitute_type _ _ _ _ _ HS (substitute_type _ _ _ _ _ HT HA)) as HCtype.
  pose proof (type_substitution_compose _ _ _ _ _ _ _ HS HT HA) as HEtype.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ HG HCtype HEtype) as HG'.
  exists a, m; split; [eapply eval_exp_sub; eassumption |].
  split; [eapply eval_exp_sub; eassumption |].
  eapply glued_term_expression_change; [exact HU | exact HC | exact HG' | |].
  - exact (wf_exp_sub _ _ _ _ _ HS (wf_exp_sub _ _ _ _ _ HT HM)).
  - eapply convert_equality; [eapply wf_exp_eq_sub_compose; eassumption | exact HCtype | exact HEtype].
Qed.

Lemma gluing_code_at_substitution : forall k Θ Γ σ i M m R,
    i < k -> wf_sub Θ Γ σ ->
    glued_type (gluing_universes k) Θ i (a_sub M σ) m R ->
    glued_term (gluing_universes k) Θ (a_sub (a_typ i) σ) (a_sub M σ) (d_univ i) m.
Proof.
  intros k Θ Γ σ i M m R Hlt HS HG.
  pose proof (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  eapply glued_term_type_change.
  - exact (type_gluing_as_term _ _ _ _ _ _ Hlt HG).
  - exact (substitute_type _ _ _ _ _ HS (wf_typ _ _ HΓ)).
  - apply wf_exp_eq_sym; exact (wf_exp_eq_typ_sub _ _ _ i HS).
Qed.

Lemma gluing_type_literal : forall k Γ i, S i < k ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ (S i)) (a_typ i).
Proof.
  intros k Γ i Hlt Θ σ ρ HE.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  pose proof (glued_type_univ _ _ _ _ HΘ (gluing_universes_lookup k i ltac:(lia))) as HUi.
  exists (d_univ (S i)), (d_univ i); split; [constructor |].
  split; [constructor |].
  eapply gluing_code_at_substitution; [exact Hlt | exact HS |].
  eapply glued_type_convert; [exact HUi | eapply substitute_type; [exact HS | now apply wf_typ] |].
  apply wf_exp_eq_sym; exact (wf_exp_eq_typ_sub _ _ _ i HS).
Qed.

Lemma gluing_natural_code : forall k Γ, 0 < k ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ 0) a_nat.
Proof.
  intros k Γ Hlt Θ σ ρ HE.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  exists (d_univ 0), d_nat; split; [constructor |].
  split; [constructor |].
  eapply gluing_code_at_substitution; [exact Hlt | exact HS |].
  eapply glued_type_convert; [exact (glued_type_nat _ _ HΘ) | eapply substitute_type; [exact HS | now apply wf_nat] |].
  apply wf_exp_eq_sym; exact (wf_exp_eq_nat_sub _ _ _ HS).
Qed.

Lemma natural_under_substitution : forall U Γ Θ σ M N r m,
    wf_sub Θ Γ σ -> wf_exp Γ a_nat M ->
    wf_exp_eq Θ a_nat (a_sub M σ) N ->
    natural_realizes Θ N r -> nat_rel r m ->
    glued_term U Θ (a_sub a_nat σ) (a_sub M σ) d_nat m.
Proof.
  intros U Γ Θ σ M N r m HS HM HE HR Hrel.
  pose proof (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  pose proof (substitute_type _ _ _ _ _ HS (wf_nat _ HΓ)) as HNs.
  pose proof (wf_exp_eq_nat_sub _ _ _ HS) as HN.
  eapply glued_term_type_change; [|exact HNs|exact (wf_exp_eq_sym _ _ _ _ HN)].
  eapply natural_glued_term; [|exact Hrel].
  eapply realizes_conversion; [|exact HE|exact HR].
  exact (convert_expression _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HS HM) (wf_nat _ HΘ) HN).
Qed.

Lemma gluing_zero : forall U Γ, typing_respects_gluing U Γ a_nat a_zero.
Proof.
  intros U Γ Θ σ ρ HE.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  exists d_nat, d_zero; split; [constructor |].
  split; [constructor |].
  eapply natural_under_substitution;
    [exact HS | exact (wf_zero _ HΓ) | exact (wf_exp_eq_zero_sub _ _ _ HS)
     | exact (realizes_zero _ HΘ) | apply nat_rel_zero].
Qed.

Lemma gluing_succ : forall U Γ M,
    universe_invariants U -> universe_coherence U ->
    wf_exp Γ a_nat M -> typing_respects_gluing U Γ a_nat M ->
    typing_respects_gluing U Γ a_nat (a_succ M).
Proof.
  intros U Γ M HU HC HM IH Θ σ ρ HE.
  destruct (IH _ _ _ HE) as (a & m & HA & He & HG).
  inversion HA; subst a.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (proj1 (substitution_contexts _ _ _ HS)) as HΘ.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ HG (wf_nat _ HΘ) (wf_exp_eq_nat_sub _ _ _ HS)) as Hnat.
  destruct (glued_term_as_natural _ _ _ _ HU HC Hnat) as (r & HR & Hrel).
  exists d_nat, (d_succ m); split; [constructor |].
  split; [now constructor |].
  eapply natural_under_substitution;
    [exact HS | now apply wf_succ | exact (wf_exp_eq_succ_sub _ _ _ _ HS HM)
     | exact (realizes_succ _ _ _ HR) | now apply nat_rel_succ].
Qed.


Lemma move_candidate : forall U Γ Δ i j A B a b R T Θ σ τ k V M N m n,
    universe_invariants U -> universe_coherence U ->
    glued_type U Γ i A a R -> glued_type U Δ j B b T ->
    weakening Θ Γ σ -> weakening Θ Δ τ ->
    at_type k a b V -> V m n ->
    R Θ σ M m -> wf_exp Θ (a_sub B τ) N ->
    wf_exp_eq Θ (a_sub A σ) M N -> T Θ τ N n.
Proof.
  intros U Γ Δ i j A B a b R T Θ σ τ k V M N m n
    HU HC HA HB Hσ Hτ HV Hmn HR HN HE.
  destruct (candidate_has_invariants _ _ _ _ _ _ HA _ _ _ _ Hσ HR) as (HM & _).
  assert (HNE : wf_exp_eq Θ (a_sub B τ) M N).
  { eapply type_gluing_move_eq; [exact HU | exact HA | exact HB | exact Hσ | exact Hτ | exact HV | exact HE]. }
  exact (proj1 (glued_candidates_aligned _ HU HC _ _ _ _ _ HA _ _ _ _ _ HB
         _ _ _ _ _ _ _ _ _ Hσ Hτ HM HN HE HNE HV Hmn) HR).
Qed.

Lemma move_same_candidate : forall U Γ Δ i j A B a R T Θ σ τ M N m,
    universe_invariants U -> universe_coherence U ->
    glued_type U Γ i A a R -> glued_type U Δ j B a T ->
    weakening Θ Γ σ -> weakening Θ Δ τ ->
    R Θ σ M m -> wf_exp Θ (a_sub B τ) N ->
    wf_exp_eq Θ (a_sub A σ) M N -> T Θ τ N m.
Proof.
  intros U Γ Δ i j A B a R T Θ σ τ M N m HU HC HA HB Hσ Hτ HR HN HE.
  destruct (candidate_has_invariants _ _ _ _ _ _ HA _ _ _ _ Hσ HR) as (_ & (k & V & HV & Hm) & _).
  eapply move_candidate; [exact HU | exact HC | exact HA | exact HB | exact Hσ | exact Hτ
                       | exact HV | exact Hm | exact HR | exact HN | exact HE].
Qed.

Lemma move_same_candidate_at_id : forall U Θ i j A B a R T M N m,
    universe_invariants U -> universe_coherence U ->
    glued_type U Θ i A a R -> glued_type U Θ j B a T ->
    R Θ a_id M m -> wf_exp Θ B N ->
    wf_exp_eq Θ A M N -> T Θ a_id N m.
Proof.
  intros U Θ i j A B a R T M N m HU HC HA HB HR HN HE.
  pose proof (glued_type_well_formed _ _ _ _ _ _ HA) as HAw.
  pose proof (glued_type_well_formed _ _ _ _ _ _ HB) as HBw.
  pose proof (expression_context _ _ _ HAw) as HΘ.
  pose proof (weakening_identity _ HΘ) as Hid.
  pose proof (wf_sub_id _ HΘ) as HIt.
  pose proof (substitute_type _ _ _ _ _ HIt HAw) as HAi.
  pose proof (substitute_type _ _ _ _ _ HIt HBw) as HBi.
  eapply move_same_candidate; [exact HU | exact HC | exact HA | exact HB | exact Hid | exact Hid | exact HR | |].
  - eapply convert_expression; [exact HN | exact HBi | apply wf_exp_eq_sym; now apply type_substitution_identity].
  - eapply convert_equality; [exact HE | exact HAi | apply wf_exp_eq_sym; now apply type_substitution_identity].
Qed.

Lemma observation_after_weakening : forall Γ Δ Θ i A a σ τ M m,
    wf_exp Γ (a_typ i) A ->
    weakening Δ Γ σ -> weakening Θ Δ τ ->
    wf_exp Δ (a_sub A σ) M /\ semantic_member a m /\ term_under_weakening Δ (a_sub A σ) M a m ->
    wf_exp Θ (a_sub A (a_compose σ τ)) (a_sub M τ) /\ semantic_member a m /\
    term_under_weakening Θ (a_sub A (a_compose σ τ)) (a_sub M τ) a m.
Proof.
  intros Γ Δ Θ i A a σ τ M m HA Hσ Hτ (HM & Hmem & HQ).
  pose proof (weakening_is_typed _ _ _ Hσ) as HS.
  pose proof (weakening_is_typed _ _ _ Hτ) as HT.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HC.
  pose proof (substitute_type _ _ _ _ _ HC HA) as HTy.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_compose _ _ _ _ _ _ _ HT HS HA)) as HE.
  split; [exact (convert_expression _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HT HM) HTy HE) |].
  split; [exact Hmem |].
  eapply convert_term_under_weakening; [exact HTy | exact HE |].
  exact (weaken_term_quote _ _ _ _ _ _ _ Hτ HM HQ).
Qed.

Lemma observations_compose : forall Γ Δ Θ Ξ i A σ τ ω M,
    wf_exp Γ (a_typ i) A ->
    weakening Δ Γ σ -> weakening Θ Δ τ -> weakening Ξ Θ ω ->
    wf_exp Δ (a_sub A σ) M ->
    wf_exp_eq Ξ (a_sub A (a_compose σ (a_compose τ ω)))
      (a_sub M (a_compose τ ω)) (a_sub (a_sub M τ) ω).
Proof.
  intros Γ Δ Θ Ξ i A σ τ ω M HA Hσ Hτ Hω HM.
  pose proof (weakening_is_typed _ _ _ Hσ) as HS.
  pose proof (weakening_is_typed _ _ _ Hτ) as HT.
  pose proof (weakening_is_typed _ _ _ Hω) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HW HT) as HTW.
  pose proof (wf_sub_compose _ _ _ _ _ HTW HS) as HC.
  eapply convert_equality.
  - exact (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HW HT HM).
  - exact (substitute_type _ _ _ _ _ HC HA).
  - apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HTW HS HA).
Qed.

Lemma instantiated_under_observation : forall Γ Δ Θ i A B σ τ X,
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    weakening Δ Γ σ -> weakening Θ Δ τ ->
    wf_exp Θ (a_sub A (a_compose σ τ)) X ->
    wf_exp Θ (a_typ i) (a_sub B (a_extend (a_compose σ τ) X)).
Proof.
  intros; eapply substitute_type; [|eassumption].
  eapply wf_sub_extend; [eapply weakening_is_typed, weakening_compose; eassumption | eassumption | eassumption].
Qed.

Definition universe_weakening (U : list universe_candidate) :=
  forall i P, nth_error U i = Some P ->
    forall Γ A a, P Γ A a -> forall Θ τ, weakening Θ Γ τ -> P Θ (a_sub A τ) a.

Lemma gluing_universes_weaken : forall k, universe_weakening (gluing_universes k).
Proof.
  intros k i P HP.
  assert (Hlt : i < k).
  { rewrite <- gluing_universes_length; apply nth_error_Some; rewrite HP; discriminate. }
  rewrite gluing_universes_lookup in HP by exact Hlt; injection HP as <-.
  intros Γ A a (R & HR) Θ τ Hτ.
  exists (fun Ξ σ => R Ξ (a_compose τ σ)).
  eapply glued_type_shift; eassumption.
Qed.

Definition candidate_weakening Γ (R : candidate) :=
  forall Δ Θ σ τ M m, weakening Δ Γ σ -> weakening Θ Δ τ ->
    R Δ σ M m -> R Θ (a_compose σ τ) (a_sub M τ) m.

Lemma weakening_as_instance : forall Γ Δ Θ i A B σ τ M,
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    weakening Δ Γ σ -> weakening Θ Δ τ ->
    wf_exp Δ (a_sub (a_pi A B) σ) M ->
    wf_exp Θ (a_pi (a_sub A (a_compose σ τ)) (a_sub B (Syntax.q (a_compose σ τ)))) (a_sub M τ).
Proof.
  intros; eapply (proj1 (proj2 (proj2 (canonical_binder_after_weakening _ _ _ _ _ _ _ _ _ _ _
    H H0 H1 H2 wf_pi wf_exp_eq_pi_sub H3 (reflexive_expression _ _ _ H3))))).
Qed.

Lemma apply_under_weakening_typing : forall Γ Δ Θ i A B σ τ M X,
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    weakening Δ Γ σ -> weakening Θ Δ τ ->
    wf_exp Δ (a_sub (a_pi A B) σ) M ->
    wf_exp Θ (a_sub A (a_compose σ τ)) X ->
    wf_exp Θ (a_sub B (a_extend (a_compose σ τ) X)) (a_app (a_sub M τ) X).
Proof.
  intros Γ Δ Θ i A B σ τ M X HA HB Hσ Hτ HM HX.
  destruct (canonical_binder_after_weakening _ _ _ _ _ _ _ _ _ _ _
    HA HB Hσ Hτ wf_pi wf_exp_eq_pi_sub HM (reflexive_expression _ _ _ HM))
    as (HAs & HBs & HMw & _).
  destruct (at_lifted_instance _ _ _ _ _ _ _ _
    (weakening_is_typed _ _ _ (weakening_compose _ _ _ _ _ Hτ Hσ)) HA HB HX) as (HBt & HE).
  exact (convert_expression _ _ _ _ _ (wf_app _ _ _ _ _ _ HAs HBs HMw HX) HBt HE).
Qed.

Lemma project_under_weakening_typing : forall Γ Δ Θ i A B σ τ M,
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    weakening Δ Γ σ -> weakening Θ Δ τ ->
    wf_exp Δ (a_sub (a_sigma A B) σ) M ->
    wf_exp Θ (a_sub A (a_compose σ τ)) (a_fst (a_sub M τ)) /\
    wf_exp Θ (a_sub B (a_extend (a_compose σ τ) (a_fst (a_sub M τ)))) (a_snd (a_sub M τ)).
Proof.
  intros Γ Δ Θ i A B σ τ M HA HB Hσ Hτ HM.
  destruct (canonical_binder_after_weakening _ _ _ _ _ _ _ _ _ _ _
    HA HB Hσ Hτ wf_sigma wf_exp_eq_sigma_sub HM (reflexive_expression _ _ _ HM))
    as (HAs & HBs & HMw & _).
  pose proof (wf_fst _ _ _ _ _ HAs HBs HMw) as HX.
  destruct (at_lifted_instance _ _ _ _ _ _ _ _
    (weakening_is_typed _ _ _ (weakening_compose _ _ _ _ _ Hτ Hσ)) HA HB HX) as (HBt & HE).
  split; [exact HX | exact (convert_expression _ _ _ _ _ (wf_snd _ _ _ _ _ HAs HBs HMw) HBt HE)].
Qed.

Lemma weakening_applications_compose : forall Γ Δ Θ Ξ i A B σ τ ω M X,
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    weakening Δ Γ σ -> weakening Θ Δ τ -> weakening Ξ Θ ω ->
    wf_exp Δ (a_sub (a_pi A B) σ) M ->
    wf_exp Ξ (a_sub A (a_compose σ (a_compose τ ω))) X ->
    wf_exp_eq Ξ (a_sub B (a_extend (a_compose σ (a_compose τ ω)) X))
      (a_app (a_sub M (a_compose τ ω)) X) (a_app (a_sub (a_sub M τ) ω) X).
Proof.
  intros Γ Δ Θ Ξ i A B σ τ ω M X HA HB Hσ Hτ Hω HM HX.
  pose proof (weakening_compose _ _ _ _ _ Hω Hτ) as HT.
  pose proof (weakening_is_typed _ _ _ (weakening_compose _ _ _ _ _ HT Hσ)) as HS.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HS HA) HB) as HBs.
  assert (HMe : wf_exp_eq Ξ
      (a_pi (a_sub A (a_compose σ (a_compose τ ω))) (a_sub B (Syntax.q (a_compose σ (a_compose τ ω)))))
      (a_sub M (a_compose τ ω)) (a_sub (a_sub M τ) ω)).
  { eapply convert_equality;
      [exact (observations_compose _ _ _ _ _ _ _ _ _ _ (wf_pi _ _ _ _ HA HB) Hσ Hτ Hω HM)
      | exact (wf_pi _ _ _ _ HAs HBs) | exact (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB)]. }
  destruct (at_lifted_instance _ _ _ _ _ _ _ _ HS HA HB HX) as (HBt & HE).
  eapply convert_equality;
    [exact (wf_exp_eq_app_cong _ _ _ _ _ _ _ _ HAs HBs HMe (reflexive_expression _ _ _ HX))
    | exact HBt | exact HE].
Qed.

Lemma weakening_projections_compose : forall Γ Δ Θ Ξ i A B σ τ ω M,
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    weakening Δ Γ σ -> weakening Θ Δ τ -> weakening Ξ Θ ω ->
    wf_exp Δ (a_sub (a_sigma A B) σ) M ->
    let s := a_compose σ (a_compose τ ω) in
    let P := a_sub M (a_compose τ ω) in
    let Q := a_sub (a_sub M τ) ω in
    wf_exp_eq Ξ (a_sub A s) (a_fst P) (a_fst Q) /\
    wf_exp_eq Ξ (a_sub B (a_extend s (a_fst P))) (a_snd P) (a_snd Q).
Proof.
  intros Γ Δ Θ Ξ i A B σ τ ω M HA HB Hσ Hτ Hω HM; cbn zeta.
  pose proof (weakening_compose _ _ _ _ _ Hω Hτ) as HT.
  pose proof (weakening_is_typed _ _ _ (weakening_compose _ _ _ _ _ HT Hσ)) as HS.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HS HA) HB) as HBs.
  pose proof (wf_sigma _ _ _ _ HAs HBs) as HΣ.
  assert (HMe : wf_exp_eq Ξ
      (a_sigma (a_sub A (a_compose σ (a_compose τ ω))) (a_sub B (Syntax.q (a_compose σ (a_compose τ ω)))))
      (a_sub M (a_compose τ ω)) (a_sub (a_sub M τ) ω)).
  { eapply convert_equality;
      [exact (observations_compose _ _ _ _ _ _ _ _ _ _ (wf_sigma _ _ _ _ HA HB) Hσ Hτ Hω HM)
      | exact HΣ | exact (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB)]. }
  split; [exact (wf_exp_eq_fst_cong _ _ _ _ _ _ HAs HBs HMe) |].
  destruct (project_under_weakening_typing _ _ _ _ _ _ _ _ _ HA HB Hσ HT HM) as (HX & HY).
  destruct (at_lifted_instance _ _ _ _ _ _ _ _ HS HA HB HX) as (HBt & HE).
  exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_snd_cong _ _ _ _ _ _ HAs HBs HMe) HBt HE).
Qed.

Lemma weakened_reflexivity : forall Γ Δ Θ i A X Y σ τ M Z,
    wf_exp Γ (a_typ i) A -> wf_exp Γ A X -> wf_exp Γ A Y ->
    weakening Δ Γ σ -> weakening Θ Δ τ ->
    wf_exp Δ (a_sub A σ) Z ->
    wf_exp_eq Δ (a_sub A σ) Z (a_sub X σ) ->
    wf_exp_eq Δ (a_sub A σ) Z (a_sub Y σ) ->
    wf_exp_eq Δ (a_sub (a_eq A X Y) σ) M (a_refl (a_sub A σ) Z) ->
    let s := a_compose σ τ in
    let Zs := a_sub Z τ in
    wf_exp_eq Θ (a_sub A s) Zs (a_sub X s) /\
    wf_exp_eq Θ (a_sub A s) Zs (a_sub Y s) /\
    wf_exp_eq Θ (a_sub (a_eq A X Y) s) (a_sub M τ) (a_refl (a_sub A s) Zs).
Proof.
  intros Γ Δ Θ i A X Y σ τ M Z HA HX HY Hσ Hτ HZ HZX HZY HME; cbn zeta.
  pose proof (weakening_is_typed _ _ _ Hσ) as HS.
  pose proof (weakening_is_typed _ _ _ Hτ) as HT.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HC.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (substitute_type _ _ _ _ _ HC HA) as HAt.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_compose _ _ _ _ _ _ _ HT HS HA)) as HAtE.
  assert (HZXt : forall V, wf_exp Γ A V -> wf_exp_eq Δ (a_sub A σ) Z (a_sub V σ) ->
    wf_exp_eq Θ (a_sub A (a_compose σ τ)) (a_sub Z τ) (a_sub V (a_compose σ τ))).
  {
    intros V HV HVeq.
    eapply wf_exp_eq_trans.
    - eapply convert_equality; [eapply wf_exp_eq_sub_cong; [exact HVeq | now apply reflexive_substitution] | exact HAt | exact HAtE].
    - apply wf_exp_eq_sym; exact (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HT HS HV).
  }
  pose proof (HZXt _ HX HZX) as HXZ.
  pose proof (HZXt _ HY HZY) as HYZ.
  split; [exact HXZ |]. split; [exact HYZ |].
  pose proof (wf_eq _ _ _ _ _ HA HX HY) as HQ.
  pose proof (substitute_type _ _ _ _ _ HC HQ) as HQt.
  eapply wf_exp_eq_trans.
  - eapply convert_equality;
      [eapply wf_exp_eq_sub_cong; [exact HME | now apply reflexive_substitution] | exact HQt |].
    apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HT HS HQ).
  - pose proof (wf_exp_sub _ _ _ _ _ HT HZ) as HZt.
    pose proof (substitute_type _ _ _ _ _ HT HAs) as HAt'.
    assert (Hann : wf_exp_eq Θ (a_typ i) (a_sub (a_eq (a_sub A σ) Z Z) τ)
                                           (a_sub (a_eq A X Y) (a_compose σ τ))).
    {
      eapply wf_exp_eq_trans.
      - exact (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HT HAs HZ HZ).
      - eapply wf_exp_eq_trans with (M' := a_eq (a_sub A (a_compose σ τ)) (a_sub X (a_compose σ τ)) (a_sub Y (a_compose σ τ))).
        + eapply wf_exp_eq_eq_cong; [exact HAtE | |];
            (eapply convert_equality; [eassumption | exact HAt' | exact (wf_exp_eq_sym _ _ _ _ HAtE)]).
        + apply wf_exp_eq_sym; exact (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HC HA HX HY).
    }
    eapply wf_exp_eq_trans.
    + exact (convert_equality _ _ _ _ _ _
        (wf_exp_eq_refl_sub _ _ _ _ _ _ HT HAs HZ) HQt Hann).
    + eapply convert_equality; [eapply wf_exp_eq_refl_cong; [exact HAtE | now apply reflexive_expression] | exact HQt |].
      eapply wf_exp_eq_trans; [|exact Hann].
      apply wf_exp_eq_sym; exact (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HT HAs HZ HZ).
Qed.

Lemma reindex_candidate : forall U Γ i A a R Θ σ τ M m,
    universe_invariants U -> universe_coherence U ->
    glued_type U Γ i A a R ->
    weakening Θ Γ σ -> weakening Θ Γ τ ->
    R Θ σ M m -> R Θ τ M m.
Proof.
  intros U Γ i A a R Θ σ τ M m HU HC HA Hσ Hτ HR.
  destruct (candidate_has_invariants _ _ _ _ _ _ HA _ _ _ _ Hσ HR) as (HM & (k & S & HT & Hm) & _).
  eapply move_candidate; [exact HU | exact HC | exact HA | exact HA | exact Hσ | exact Hτ
                       | exact HT | exact Hm | exact HR | |now apply reflexive_expression].
  eapply type_gluing_move_term; [exact HU | exact HA | exact HA | exact Hσ | exact Hτ | exact HT | exact HM].
Qed.

Ltac weaken_observation HA Hσ Hτ HK :=
  let HM := fresh "HM" in
  let Hsem := fresh "Hsem" in
  let HQ := fresh "HQ" in
  let Hact := fresh "Hact" in
  destruct HK as (HM & Hsem & HQ & Hact);
  let HN := fresh "HN" in
  let HNsem := fresh "HNsem" in
  let HNq := fresh "HNq" in
  destruct (observation_after_weakening _ _ _ _ _ _ _ _ _ _ HA Hσ Hτ (conj HM (conj Hsem HQ)))
    as (HN & HNsem & HNq);
  split; [exact HN |]; split; [exact HNsem |]; split; [exact HNq |].

Lemma candidates_weaken : forall U Γ i A a R,
    universe_invariants U -> universe_coherence U -> universe_weakening U ->
    glued_type U Γ i A a R -> candidate_weakening Γ R.
Proof.
  intros U Γ i A a R HU HC HW H.
  induction H as
    [Γ HG
    |Γ i P HG HP
    |Γ i A k n HA HN
    |Γ i A B a ρ C R T S HS HA IHA HB HF HT IHT
    |Γ i A B a ρ C R T S HS HA IHA HB HF HT IHT
    |Γ i A X Y a x y R S HS HA IHA HX HY HRX HRY
    |Γ i A B a R HA IHA HB HE
    |Γ Γ' i A a R σ HA IHA Hσ
    |Γ i A a R K HA IHA HE
    |Γ i j A a R HA IHA Hle
    |Γ i A a b R S HA IHA HS]; intros Δ Θ δ τ M m HD HTau HK.
  - pose proof (wf_nat Γ HG) as HNat; weaken_observation HNat HD HTau HK.
    destruct Hact as (r & HR & Hrel); exists r; split; [eapply natural_realizes_weaken; eassumption | exact Hrel].
  - pose proof (wf_typ Γ i HG) as HUniv; weaken_observation HUniv HD HTau HK.
    exact (HW _ _ HP _ _ _ Hact _ _ HTau).
  - weaken_observation HA HD HTau HK.
    destruct Hact as (p & He & Hnp).
    exists p; split; [exact He|].
    pose proof (weakening_is_typed _ _ _ HD) as Hδ.
    pose proof (weakening_is_typed _ _ _ HTau) as Hτ.
    pose proof (wf_sub_compose _ _ _ _ _ Hτ Hδ) as Hc.
    eapply convert_neutral_under_weakening.
    + exact (substitute_type _ _ _ _ _ Hc HA).
    + apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ Hτ Hδ HA).
    + exact (weaken_neutral _ _ _ _ _ _ HTau HM Hnp).
  - pose proof (glued_type_well_formed _ _ _ _ _ _ HA) as HAw.
    pose proof (wf_pi _ _ _ _ HAw HB) as HP.
    weaken_observation HP HD HTau HK.
    intros Ξ ω X x Hω HX.
    pose proof (weakening_compose _ _ _ _ _ Hω HTau) as Hτw.
    pose proof (weakening_compose _ _ _ _ _ HTau HD) as Hδτ.
    pose proof (weakening_compose _ _ _ _ _ Hτw HD) as Hs.
    pose proof (weakening_compose _ _ _ _ _ Hω Hδτ) as Hs'.
    assert (HXd : R Ξ (a_compose δ (a_compose τ ω)) X x).
    { eapply reindex_candidate; [exact HU | exact HC | exact HA | exact Hs' | exact Hs | exact HX]. }
    destruct (Hact _ _ _ _ Hτw HXd) as (b & y & Hb & Hy & HR).
    pose proof (HT _ _ _ _ Hs HXd _ Hb) as G1.
    pose proof (HT _ _ _ _ Hs' HX _ Hb) as G2.
    destruct (candidate_has_invariants _ _ _ _ _ _ HA _ _ _ _ Hs HXd) as (HXa & _).
    destruct (candidate_has_invariants _ _ _ _ _ _ HA _ _ _ _ Hs' HX) as (HXb & _).
    exists b, y; split; [exact Hb |]. split; [exact Hy |].
    eapply move_same_candidate_at_id;
      [exact HU | exact HC | exact G1 | exact G2 | exact HR | |].
    + exact (apply_under_weakening_typing _ _ _ _ _ _ _ _ _ _ HAw HB Hδτ Hω HN HXb).
    + exact (weakening_applications_compose _ _ _ _ _ _ _ _ _ _ _ _ HAw HB HD HTau Hω HM HXa).
  - pose proof (glued_type_well_formed _ _ _ _ _ _ HA) as HAw.
    pose proof (wf_sigma _ _ _ _ HAw HB) as HP.
    weaken_observation HP HD HTau HK.
    intros Ξ ω Hω.
    pose proof (weakening_compose _ _ _ _ _ Hω HTau) as Hτw.
    pose proof (weakening_compose _ _ _ _ _ HTau HD) as Hδτ.
    pose proof (weakening_compose _ _ _ _ _ Hτw HD) as Hs.
    pose proof (weakening_compose _ _ _ _ _ Hω Hδτ) as Hs'.
    destruct (Hact _ _ Hτw) as (x & y & b & Hx & Hy & Hb & HRf & HRs).
    destruct (weakening_projections_compose _ _ _ _ _ _ _ _ _ _ _ HAw HB HD HTau Hω HM) as (E1 & E2).
    destruct (project_under_weakening_typing _ _ _ _ _ _ _ _ _ HAw HB Hδτ Hω HN) as (Hxf & Hyf).
    assert (HRf' : R Ξ (a_compose (a_compose δ τ) ω) (a_fst (a_sub (a_sub M τ) ω)) x).
    { eapply move_same_candidate; [exact HU | exact HC | exact HA | exact HA | exact Hs | exact Hs' | exact HRf | exact Hxf | exact E1]. }
    pose proof (HT _ _ _ _ Hs HRf _ Hb) as G1.
    pose proof (HT _ _ _ _ Hs' HRf' _ Hb) as G2.
    exists x, y, b; split; [exact Hx |]. split; [exact Hy |]. split; [exact Hb |]. split; [exact HRf' |].
    eapply move_same_candidate_at_id; [exact HU | exact HC | exact G1 | exact G2 | exact HRs | exact Hyf | exact E2].
  - pose proof (glued_type_well_formed _ _ _ _ _ _ HA) as HAw.
    pose proof (wf_eq _ _ _ _ _ HAw HX HY) as HE.
    weaken_observation HE HD HTau HK.
    destruct Hact as [(b & n & -> & Hn) | (Z & z & -> & HZ & HZX & HZY & HR)].
    + left; exists b, n; split; [reflexivity |].
      pose proof (weakening_is_typed _ _ _ HD) as Hδ.
      pose proof (weakening_is_typed _ _ _ HTau) as Hτ.
      pose proof (wf_sub_compose _ _ _ _ _ Hτ Hδ) as Hc.
      eapply convert_neutral_under_weakening.
      * exact (substitute_type _ _ _ _ _ Hc HE).
      * apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ Hτ Hδ HE).
      * exact (weaken_neutral _ _ _ _ _ _ HTau HM Hn).
    + right; exists (a_sub Z τ), z; split; [reflexivity |].
      split; [exact (IHA _ _ _ _ _ _ HD HTau HZ) |].
      destruct (candidate_has_invariants _ _ _ _ _ _ HA _ _ _ _ HD HZ) as (HZwf & _).
      exact (weakened_reflexivity _ _ _ _ _ _ _ _ _ _ _ HAw HX HY HD HTau HZwf HZX HZY HR).
  - exact (IHA _ _ _ _ _ _ HD HTau HK).
  - pose proof (weakening_compose _ _ _ _ _ HD Hσ) as HD'.
    pose proof (weakening_compose _ _ _ _ _ HTau HD) as Ht'.
    pose proof (weakening_compose _ _ _ _ _ Ht' Hσ) as Ht''.
    pose proof (weakening_compose _ _ _ _ _ HTau HD') as Hr.
    eapply reindex_candidate; [exact HU | exact HC | exact HA | exact Hr | exact Ht'' | exact (IHA _ _ _ _ _ _ HD' HTau HK)].
  - apply HE; [eapply weakening_compose; eassumption |].
    eapply IHA; [exact HD | exact HTau | apply HE; assumption].
  - exact (IHA _ _ _ _ _ _ HD HTau HK).
  - destruct HK as (p & HK & Hrel); exists p; split; [exact (IHA _ _ _ _ _ _ HD HTau HK) | exact Hrel].
Qed.

Lemma glued_term_weaken : forall U Γ Δ A M a m τ,
    universe_invariants U -> universe_coherence U -> universe_weakening U ->
    weakening Δ Γ τ -> glued_term U Γ A M a m ->
    glued_term U Δ (a_sub A τ) (a_sub M τ) a m.
Proof.
  intros U Γ Δ A M a m τ HU HC HW Hτ (i & R & HA & HK).
  pose proof (glued_type_shift _ _ _ _ _ _ _ _ HA Hτ) as HAT.
  pose proof (glued_type_well_formed _ _ _ _ _ _ HA) as HAw.
  pose proof (glued_type_well_formed _ _ _ _ _ _ HAT) as HAt.
  pose proof (weakening_identity _ (expression_context _ _ _ HAw)) as Hid.
  pose proof (weakening_identity _ (expression_context _ _ _ HAt)) as Hid'.
  pose proof (weakening_compose _ _ _ _ _ Hτ Hid) as Hs.
  pose proof (weakening_compose _ _ _ _ _ Hid' Hτ) as Hs'.
  exists i, (fun Θ σ => R Θ (a_compose τ σ)); split; [exact HAT |].
  eapply reindex_candidate; [exact HU | exact HC | exact HA | exact Hs | exact Hs' |].
  exact (candidates_weaken _ _ _ _ _ _ HU HC HW HA _ _ _ _ _ _ Hid Hτ HK).
Qed.

Lemma glued_environment_weaken : forall U Θ Γ σ ρ,
    universe_invariants U -> universe_coherence U -> universe_weakening U ->
    glued_environment U Θ Γ σ ρ ->
    forall Ξ τ, weakening Ξ Θ τ -> glued_environment U Ξ Γ (a_compose σ τ) ρ.
Proof.
  intros U Θ Γ σ ρ HU HC HW HE.
  induction HE as [σ ρ Hσ | Γ A i σ ρ a Hσ HA Htail IH HV HM Hcan]; intros Ξ τ Hτ;
    pose proof (weakening_is_typed _ _ _ Hτ) as HT;
    pose proof (wf_sub_compose _ _ _ _ _ HT Hσ) as HS.
  - now apply glued_environment_empty.
  - pose proof (proj2 (substitution_contexts _ _ _ Hσ)) as HG.
    pose proof (wf_sub_weaken _ _ HG) as HD.
    pose proof (wf_sub_compose _ _ _ _ _ Hσ HD) as HDσ.
    pose proof (wf_sub_compose _ _ _ _ _ HT HDσ) as HP.
    pose proof (wf_sub_compose _ _ _ _ _ HS HD) as HP'.
    pose proof (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HD Hσ HT) as HE.
    pose proof (substitute_type _ _ _ _ _ HP' HA) as HAt.
    assert (HAtE : wf_exp_eq Ξ (a_typ i)
      (a_sub (a_sub A (a_compose a_weaken σ)) τ) (a_sub A (a_compose a_weaken (a_compose σ τ)))).
    {
      eapply wf_exp_eq_trans;
        [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HT HDσ HA) |].
      eapply substitute_type_equality; [exact HP | exact HE | now apply reflexive_expression].
    }
    pose proof (type_of_first_variable _ _ HG) as H0.
    assert (Hterm : wf_exp Ξ (a_sub A (a_compose a_weaken (a_compose σ τ)))
        (a_sub (a_var 0) (a_compose σ τ))).
    {
      eapply convert_expression; [exact (wf_exp_sub _ _ _ _ _ HS H0) | exact HAt |].
      apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HS HD HA).
    }
    pose proof (glued_term_weaken _ _ _ _ _ _ _ _ HU HC HW Hτ HM) as HMw.
    eapply glued_environment_cons.
    + exact HS.
    + exact HA.
    + eapply glued_environment_conversion; [exact HU | exact HC | exact (IH _ _ Hτ) | exact HP' | exact HE].
    + exact HV.
    + eapply glued_term_expression_change;
        [exact HU | exact HC
         | exact (glued_term_type_change _ _ _ _ _ _ _ _ HMw HAt HAtE)
         | exact Hterm |].
      eapply convert_equality; [apply wf_exp_eq_sym; exact (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HT Hσ H0) | exact HAt |].
      apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HS HD HA).
    + exact Hcan.
Qed.

Lemma glued_code_from_term : forall k Θ i M a,
    i < k ->
    glued_term (gluing_universes k) Θ (a_typ i) M (d_univ i) a ->
    exists R, glued_type (gluing_universes k) Θ i M a R.
Proof.
  intros k Θ i M a Hlt (j & R & Hcode & HM).
  pose proof (glued_type_well_formed _ _ _ _ _ _ Hcode) as Hty.
  pose proof (expression_context _ _ _ Hty) as HΘ.
  pose proof (weakening_identity _ HΘ) as Hid.
  pose proof (gluing_universes_lookup _ _ Hlt) as Hnth.
  pose proof (glued_type_univ _ _ _ _ HΘ Hnth) as HUniv.
  destruct (candidate_has_invariants _ _ _ _ _ _ Hcode _ _ _ _ Hid HM)
    as (HMi & (l & V & HV & Hoa) & _).
  pose proof (typed_universe_value i) as Hmodel.
  assert (Ha : type_rel (universes i) a a).
  { exact (proj1 (at_type_coherent_l _ _ _ _ _ _ _ HV Hmodel _ _) Hoa). }
  pose proof (reflexive_expression _ _ _ HMi) as Hrefl.
  destruct (move_candidate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (gluing_universes_quote k) (gluing_universes_coherent k) Hcode HUniv
    Hid Hid Hmodel Ha HM HMi Hrefl) as (_ & _ & _ & T & HT).
  unfold gluing_universe in HT; rewrite gluing_universes_length in HT.
  exists T; eapply (glued_type_at_prefix i k); [lia | lia | exact HT].
Qed.

Lemma reflect_glued_term : forall U Γ i A M a R n,
    universe_invariants U ->
    glued_type U Γ i A a R ->
    wf_exp Γ A M -> neutral_under_weakening Γ A M n ->
    glued_term U Γ A M a (d_neut a n).
Proof.
  intros U Γ i A M a R n HU HA HM HN.
  exists i, R; split; [exact HA |].
  destruct (quoted_candidate_reflects _ _ _ _ _ _ HU HA) as (HQ & HR).
  exact (reflect_at_identity _ _ _ _ _ _ _ HQ HR HM HN).
Qed.

Lemma instantiate_glued_environment : forall U Γ Θ Ξ σ τ ρ A i X x a,
    universe_invariants U -> universe_coherence U -> universe_weakening U ->
    glued_environment U Θ Γ σ ρ ->
    weakening Ξ Θ τ -> wf_exp Γ (a_typ i) A -> eval_exp A ρ a ->
    glued_term U Ξ (a_sub A (a_compose σ τ)) X a x ->
    glued_environment U Ξ (A :: Γ) (a_extend (a_compose σ τ) X) (extend_env ρ x).
Proof.
  intros.
  eapply glued_environment_extend;
    [eassumption | eassumption | eapply glued_environment_weaken; eassumption | eassumption | eassumption | eassumption].
Qed.

Lemma lift_glued_environment_as : forall U Γ Θ σ ρ A D i a R,
    universe_invariants U -> universe_coherence U -> universe_weakening U ->
    glued_environment U Θ Γ σ ρ ->
    wf_exp Γ (a_typ i) A -> eval_exp A ρ a ->
    glued_type U Θ i D a R ->
    wf_exp_eq Θ (a_typ i) D (a_sub A σ) ->
    glued_environment U (D :: Θ) (A :: Γ) (Syntax.q σ)
      (extend_env ρ (d_neut a (d_var (length Θ)))).
Proof.
  intros U Γ Θ σ ρ A D i a R HU HC HW HE HA HV HG HDA.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (glued_type_well_formed _ _ _ _ _ _ HG) as HD.
  pose proof (proj1 (substitution_contexts _ _ _ HS)) as HΘ.
  pose proof (wf_ctx_extend _ _ _ HΘ HD) as HΘA.
  pose proof (weakening_drop _ _ HΘA) as Hwk.
  pose proof (weakening_is_typed _ _ _ Hwk) as HT.
  pose proof (type_of_first_variable _ _ HΘA) as HX.
  pose proof (variable_neutral_under_weakening _ _ _ HΘA (here D Θ)) as HN.
  cbn [length Nat.sub] in HN; rewrite Nat.sub_0_r in HN.
  pose proof (glued_type_shift _ _ _ _ _ _ _ _ HG Hwk) as Hshift.
  pose proof (reflect_glued_term _ _ _ _ _ _ _ _ HU Hshift HX HN) as Hvar.
  pose proof (substitute_type _ _ _ _ _ (wf_sub_compose _ _ _ _ _ HT HS) HA) as HTy.
  assert (HEq : wf_exp_eq (D :: Θ) (a_typ i) (a_sub D a_weaken) (a_sub A (a_compose σ a_weaken))).
  {
    eapply wf_exp_eq_trans.
    - eapply substitute_type_equality; [exact HT | now apply reflexive_substitution | exact HDA].
    - apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HT HS HA).
  }
  exact (instantiate_glued_environment _ _ _ _ _ _ _ _ _ _ _ _ HU HC HW HE Hwk HA HV
     (glued_term_type_change _ _ _ _ _ _ _ _ Hvar HTy HEq)).
Qed.

Lemma lift_glued_environment : forall U Γ Θ σ ρ A i a R,
    universe_invariants U -> universe_coherence U -> universe_weakening U ->
    glued_environment U Θ Γ σ ρ ->
    wf_exp Γ (a_typ i) A -> eval_exp A ρ a ->
    glued_type U Θ i (a_sub A σ) a R ->
    glued_environment U (a_sub A σ :: Θ) (A :: Γ) (Syntax.q σ)
      (extend_env ρ (d_neut a (d_var (length Θ)))).
Proof.
  intros U Γ Θ σ ρ A i a R HU HC HW HE HA HV HG.
  eapply lift_glued_environment_as;
    [exact HU | exact HC | exact HW | exact HE | exact HA | exact HV | exact HG |].
  apply reflexive_expression.
  exact (glued_type_well_formed _ _ _ _ _ _ HG).
Qed.

Lemma typed_lift_instantiation : forall Γ Δ Θ σ τ i A X,
    wf_sub Θ Δ τ -> wf_sub Δ Γ σ -> wf_exp Γ (a_typ i) A ->
    wf_exp Θ (a_sub A (a_compose σ τ)) X ->
    wf_sub Θ (a_sub A σ :: Δ) (a_extend τ X) /\
    wf_sub_eq Θ (A :: Γ)
      (a_compose (Syntax.q σ) (a_extend τ X)) (a_extend (a_compose σ τ) X).
Proof.
  intros Γ Δ Θ σ τ i A X HT HS HA HX.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (substitute_type _ _ _ _ _ HT HAs) as HASt.
  pose proof (type_substitution_compose _ _ _ _ _ _ _ HT HS HA) as HST.
  pose proof (convert_expression _ _ _ _ _ HX HASt HST) as HX'.
  pose proof (wf_sub_extend _ _ _ _ _ _ HT HAs HX') as HE.
  pose proof (proj2 (substitution_contexts _ _ _ HE)) as HG.
  pose proof (wf_sub_weaken _ _ HG) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HW HS) as HSW.
  pose proof (wf_sub_compose _ _ _ _ _ HE HSW) as HSWX.
  split; [exact HE |].
  assert (H0 : wf_exp (a_sub A σ :: Δ) (a_sub A (a_compose σ a_weaken)) (a_var 0)).
  { eapply convert_expression; [now apply type_of_first_variable | eapply substitute_type; eassumption |].
    apply wf_exp_eq_sym; eapply type_substitution_compose; eassumption. }
  assert (Htail : wf_sub_eq Θ Γ (a_compose (a_compose σ a_weaken) (a_extend τ X)) (a_compose σ τ)).
  {
    eapply wf_sub_eq_trans; [exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HS HW HE) |].
    eapply wf_sub_eq_compose_cong.
    - exact (wf_sub_eq_p_extend _ _ _ _ _ _ HT HAs HX').
    - now apply reflexive_substitution.
  }
  unfold Syntax.q.
  eapply wf_sub_eq_trans.
  - exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ HSW HA H0 HE).
  - eapply wf_sub_eq_extend_cong; [exact Htail | exact HA |].
    eapply convert_equality; [exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ HT HAs HX') | eapply substitute_type; eassumption |].
    apply wf_exp_eq_sym.
    eapply wf_exp_eq_trans; [|exact HST].
    eapply substitute_type_equality; [exact HSWX | exact Htail | now apply reflexive_expression].
Qed.

Lemma type_after_lift_instantiation : forall Γ Δ Θ σ τ i j A X B,
    wf_sub Θ Δ τ -> wf_sub Δ Γ σ -> wf_exp Γ (a_typ i) A ->
    wf_exp Θ (a_sub A (a_compose σ τ)) X -> wf_exp (A :: Γ) (a_typ j) B ->
    wf_exp_eq Θ (a_typ j) (a_sub (a_sub B (Syntax.q σ)) (a_extend τ X))
                         (a_sub B (a_extend (a_compose σ τ) X)).
Proof.
  intros Γ Δ Θ σ τ i j A X B HT HS HA HX HB.
  destruct (typed_lift_instantiation _ _ _ _ _ _ _ _ HT HS HA HX) as (HE & Hq).
  pose proof (lift_substitution _ _ _ _ _ HS HA) as HQt.
  eapply wf_exp_eq_trans.
  - apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HE HQt HB).
  - eapply substitute_type_equality; [exact (wf_sub_compose _ _ _ _ _ HE HQt) | exact Hq | now apply reflexive_expression].
Qed.

Lemma expression_after_lift_instantiation : forall Γ Δ Θ σ τ i A X B M,
    wf_sub Θ Δ τ -> wf_sub Δ Γ σ -> wf_exp Γ (a_typ i) A ->
    wf_exp Θ (a_sub A (a_compose σ τ)) X -> wf_exp (A :: Γ) B M ->
    wf_exp_eq Θ (a_sub B (a_extend (a_compose σ τ) X))
      (a_sub (a_sub M (Syntax.q σ)) (a_extend τ X)) (a_sub M (a_extend (a_compose σ τ) X)).
Proof.
  intros Γ Δ Θ σ τ i A X B M HT HS HA HX HM.
  destruct (expression_type _ _ _ HM) as (j & HB).
  destruct (typed_lift_instantiation _ _ _ _ _ _ _ _ HT HS HA HX) as (HE & Hq).
  pose proof (lift_substitution _ _ _ _ _ HS HA) as HQt.
  pose proof (wf_sub_extend _ _ _ _ _ _ (wf_sub_compose _ _ _ _ _ HT HS) HA HX) as HR.
  assert (HBT : wf_exp_eq Θ (a_typ j)
    (a_sub B (a_compose (Syntax.q σ) (a_extend τ X))) (a_sub B (a_extend (a_compose σ τ) X))).
  { eapply substitute_type_equality; [exact (wf_sub_compose _ _ _ _ _ HE HQt) | exact Hq | now apply reflexive_expression]. }
  eapply convert_equality; [|exact (substitute_type _ _ _ _ _ HR HB)|exact HBT].
  eapply wf_exp_eq_trans.
  - apply wf_exp_eq_sym; exact (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HE HQt HM).
  - eapply wf_exp_eq_sub_cong; [exact (reflexive_expression _ _ _ HM) | exact Hq].
Qed.

Lemma candidate_to_world : forall U Γ Δ i A a R σ M m,
    universe_invariants U -> universe_coherence U ->
    glued_type U Γ i A a R -> weakening Δ Γ σ ->
    R Δ σ M m -> glued_term U Δ (a_sub A σ) M a m.
Proof.
  intros U Γ Δ i A a R σ M m HU HC HA Hσ HM.
  pose proof (weakening_is_typed _ _ _ Hσ) as HS.
  pose proof (weakening_identity _ (proj1 (substitution_contexts _ _ _ HS))) as Hid.
  exists i, (fun Θ τ => R Θ (a_compose σ τ)).
  split; [exact (glued_type_shift _ _ _ _ _ _ _ _ HA Hσ) |].
  eapply reindex_candidate; [exact HU|exact HC|exact HA|exact Hσ|exact (weakening_compose _ _ _ _ _ Hid Hσ)|exact HM].
Qed.

Lemma candidate_from_world : forall U Γ Δ i A a R σ M m,
    universe_invariants U -> universe_coherence U ->
    glued_type U Γ i A a R -> weakening Δ Γ σ ->
    glued_term U Δ (a_sub A σ) M a m -> R Δ σ M m.
Proof.
  intros U Γ Δ i A a R σ M m HU HC HA Hσ (j & T & HB & HM).
  pose proof (weakening_is_typed _ _ _ Hσ) as HS.
  pose proof (weakening_identity _ (proj1 (substitution_contexts _ _ _ HS))) as Hid.
  pose proof (glued_type_shift _ _ _ _ _ _ _ _ HA Hσ) as Hshift.
  destruct (candidate_has_invariants _ _ _ _ _ _ HB _ _ _ _ Hid HM) as (HMi & _).
  assert (HMs : R Δ (a_compose σ a_id) M m).
  {
    change ((fun Ξ τ => R Ξ (a_compose σ τ)) Δ a_id M m).
    eapply move_same_candidate; [exact HU|exact HC|exact HB|exact Hshift|exact Hid|exact Hid
                                |exact HM|exact HMi|now apply reflexive_expression].
  }
  eapply reindex_candidate; [exact HU|exact HC|exact HA|exact (weakening_compose _ _ _ _ _ Hid Hσ)|exact Hσ|exact HMs].
Qed.

Lemma semantically_typed_code : forall Γ i A ρ a,
    wf_exp Γ (a_typ i) A -> env_related Γ ρ ρ ->
    eval_exp A ρ a -> exists R, at_type i a a R.
Proof.
  intros Γ i A ρ a HA HE Hv.
  destruct fundamental_evaluation as (_ & _ & Htyping & _).
  destruct (from_universe _ _ _ _ _ (proj1 (Htyping _ _ _ HA) _ _ HE))
    as (b & c & Hb & Hc & H).
  pose proof (exp_unique _ _ _ Hb _ Hv) as E; subst b.
  pose proof (exp_unique _ _ _ Hc _ Hv) as E; subst c.
  exact H.
Qed.

Lemma extract_glued_code : forall k Γ Θ σ ρ i A,
    i < k ->
    glued_environment (gluing_universes k) Θ Γ σ ρ ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    exists a R, eval_exp A ρ a /\ glued_type (gluing_universes k) Θ i (a_sub A σ) a R.
Proof.
  intros k Γ Θ σ ρ i A Hk HE HA.
  destruct (HA _ _ _ HE) as (s & a & Hs & Ha & HG); inversion Hs; subst.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (wf_typ _ i (proj1 (substitution_contexts _ _ _ HS))) as HT.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ HG HT (wf_exp_eq_typ_sub _ _ _ _ HS)) as HU.
  destruct (glued_code_from_term _ _ _ _ _ Hk HU) as (R & HR).
  exists a, R; auto.
Qed.

Definition family_closes Θ (ρ : env) B (R : candidate) :=
  forall Ξ τ X x, weakening Ξ Θ τ -> R Ξ τ X x ->
    exists b, eval_exp B (extend_env ρ x) b.

Definition family_glues U Θ i B (ρ : env) C (R : candidate)
    (T : ctx -> sub -> exp -> domain -> candidate) :=
  forall Ξ τ X x, weakening Ξ Θ τ -> R Ξ τ X x ->
    forall b, eval_exp C (extend_env ρ x) b ->
    glued_type U Ξ i (a_sub B (a_extend τ X)) b (T Ξ τ X x).

Lemma choose_glued_family : forall U Θ i B ρ C R,
    universe_invariants U -> universe_coherence U ->
    (forall Ξ τ X x, weakening Ξ Θ τ -> R Ξ τ X x ->
      exists b T, eval_exp C (extend_env ρ x) b /\ glued_type U Ξ i (a_sub B (a_extend τ X)) b T) ->
    exists T, family_closes Θ ρ C R /\ family_glues U Θ i B ρ C R T.
Proof.
  intros U Θ i B ρ C R HU HC H.
  exists (fun Ξ τ X x Ω σ M m =>
    exists b T, eval_exp C (extend_env ρ x) b /\
      glued_type U Ξ i (a_sub B (a_extend τ X)) b T /\ T Ω σ M m).
  split.
  - intros Ξ τ X x HW HX; destruct (H _ _ _ _ HW HX) as (b & T & Hb & HT); eauto.
  - intros Ξ τ X x HW HX b Hb.
    destruct (H _ _ _ _ HW HX) as (b' & T & Hb' & HT).
    pose proof (exp_unique _ _ _ Hb' _ Hb) as E; subst b'.
    eapply glued_type_extensional; [exact HT |].
    intros Ω σ M m HG; split; [eauto 8|].
    intros (c & Q & Hc & HQ & HR).
    pose proof (exp_unique _ _ _ Hc _ Hb) as E; subst c.
    destruct (candidate_has_invariants _ _ _ _ _ _ HQ _ _ _ _ HG HR) as (HM & _).
    eapply move_same_candidate; [exact HU | exact HC | exact HQ | exact HT
                                 | exact HG | exact HG | exact HR | exact HM | now apply reflexive_expression].
Qed.

Lemma construct_glued_family : forall k Γ Θ σ ρ i A B a R,
    i < k ->
    glued_environment (gluing_universes k) Θ Γ σ ρ ->
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    eval_exp A ρ a ->
    glued_type (gluing_universes k) Θ i (a_sub A σ) a R ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (a_typ i) B ->
    exists T, family_closes Θ ρ B R /\
      family_glues (gluing_universes k) Θ i (a_sub B (Syntax.q σ)) ρ B R T.
Proof.
  intros k Γ Θ σ ρ i A B a R Hk HE HA HB Hae HG HBg.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  eapply choose_glued_family; [exact HU | exact HC |].
  intros Ξ τ X x HW HX.
  pose proof (weakening_is_typed _ _ _ HW) as HT.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HST.
  pose proof (candidate_to_world _ _ _ _ _ _ _ _ _ _ HU HC HG HW HX) as HXg.
  pose proof (substitute_type _ _ _ _ _ HST HA) as HAs.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_compose _ _ _ _ _ _ _ HT HS HA)) as HAtE.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ HXg HAs HAtE) as HXg'.
  pose proof (instantiate_glued_environment _ _ _ _ _ _ _ _ _ _ _ _
    HU HC (gluing_universes_weaken k) HE HW HA Hae HXg') as HEnv.
  destruct (extract_glued_code _ _ _ _ _ _ _ Hk HEnv HBg) as (b & T & Hb & HBt).
  pose proof (glued_term_typing _ _ _ _ _ _ HXg') as HXt.
  destruct (typed_lift_instantiation _ _ _ _ _ _ _ _ HT HS HA HXt) as (HExt & HEq).
  pose proof (substitute_type _ _ _ _ _ HExt (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HS HA) HB)) as HBw.
  exists b, T; split; [exact Hb |].
  eapply glued_type_convert; [exact HBt | exact HBw |].
  apply wf_exp_eq_sym; exact (type_after_lift_instantiation _ _ _ _ _ _ _ _ _ _ HT HS HA HXt HB).
Qed.

Lemma gluing_pi : forall k Γ A B i,
    i < k ->
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (a_typ i) B ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) (a_pi A B).
Proof.
  intros k Γ A B i Hk HA HB HAg HBg Θ σ ρ HE.
  destruct (extract_glued_code _ _ _ _ _ _ _ Hk HE HAg) as (a & R & Hae & HG).
  destruct (construct_glued_family _ _ _ _ _ _ _ _ _ _ Hk HE HA HB Hae HG HBg) as (T & HF & HT).
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (wf_pi _ _ _ _ HA HB) as HP.
  assert (Heval : eval_exp (a_pi A B) ρ (d_pi a ρ B)) by now apply eval_exp_pi.
  destruct (semantically_typed_code _ _ _ _ _ HP (glued_environment_semantic _ _ _ _ _ HE) Heval) as (S & Hsem).
  pose proof (glued_type_pi _ _ _ _ _ _ _ _ _ _ _ Hsem HG
    (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HS HA) HB) HF HT) as HPI.
  exists (d_univ i), (d_pi a ρ B); split; [apply eval_exp_typ |].
  split; [exact Heval |].
  eapply gluing_code_at_substitution; [exact Hk | exact HS |].
  eapply glued_type_convert; [exact HPI | exact (substitute_type _ _ _ _ _ HS HP) |].
  apply wf_exp_eq_sym; exact (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB).
Qed.

Lemma gluing_sigma : forall k Γ A B i,
    i < k ->
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (a_typ i) B ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) (a_sigma A B).
Proof.
  intros k Γ A B i Hk HA HB HAg HBg Θ σ ρ HE.
  destruct (extract_glued_code _ _ _ _ _ _ _ Hk HE HAg) as (a & R & Hae & HG).
  destruct (construct_glued_family _ _ _ _ _ _ _ _ _ _ Hk HE HA HB Hae HG HBg) as (T & HF & HT).
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (wf_sigma _ _ _ _ HA HB) as HP.
  assert (Heval : eval_exp (a_sigma A B) ρ (d_sigma a ρ B)) by now apply eval_exp_sigma.
  destruct (semantically_typed_code _ _ _ _ _ HP (glued_environment_semantic _ _ _ _ _ HE) Heval) as (S & Hsem).
  pose proof (glued_type_sigma _ _ _ _ _ _ _ _ _ _ _ Hsem HG
    (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HS HA) HB) HF HT) as HPI.
  exists (d_univ i), (d_sigma a ρ B); split; [apply eval_exp_typ |].
  split; [exact Heval |].
  eapply gluing_code_at_substitution; [exact Hk | exact HS |].
  eapply glued_type_convert; [exact HPI | exact (substitute_type _ _ _ _ _ HS HP) |].
  apply wf_exp_eq_sym; exact (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB).
Qed.

Lemma candidate_at_identity : forall U Θ i A a R M m,
    universe_invariants U -> universe_coherence U ->
    glued_type U Θ i A a R -> glued_term U Θ A M a m ->
    R Θ a_id M m.
Proof.
  intros U Θ i A a R M m HU HC HA (j & T & HB & HM).
  pose proof (glued_type_well_formed _ _ _ _ _ _ HA) as Ht.
  pose proof (weakening_identity _ (expression_context _ _ _ Ht)) as Hid.
  destruct (candidate_has_invariants _ _ _ _ _ _ HB _ _ _ _ Hid HM) as (HMt & _).
  eapply move_same_candidate; [exact HU|exact HC|exact HB|exact HA|exact Hid|exact Hid|exact HM|exact HMt|now apply reflexive_expression].
Qed.

Lemma glued_at_candidate_identity : forall U Θ i A a R M m,
    glued_type U Θ i A a R -> R Θ a_id M m -> glued_term U Θ A M a m.
Proof. intros; eexists _, _; eauto. Qed.

Lemma type_extension_congruence : forall Θ Γ A B σ τ X Y i j,
    wf_sub Θ Γ σ -> wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ j) B ->
    wf_sub_eq Θ Γ σ τ ->
    wf_exp Θ (a_sub A σ) X -> wf_exp_eq Θ (a_sub A σ) X Y ->
    wf_exp_eq Θ (a_typ j) (a_sub B (a_extend σ X)) (a_sub B (a_extend τ Y)).
Proof.
  intros Θ Γ A B σ τ X Y i j Hσ HA HB Hsub HX HE.
  eapply substitute_type_equality;
    [exact (wf_sub_extend _ _ _ _ _ _ Hσ HA HX) | eapply wf_sub_eq_extend_cong; eassumption | now apply reflexive_expression].
Qed.

Lemma instantiated_identity_compose : forall Θ i A B X,
    wf_exp Θ (a_typ i) A -> wf_exp (A :: Θ) (a_typ i) B ->
    wf_exp Θ A X ->
    wf_exp Θ (a_sub A (a_compose a_id a_id)) X /\
    wf_exp_eq Θ (a_typ i) (a_sub B (a_extend (a_compose a_id a_id) X)) (a_sub B (a_extend a_id X)).
Proof.
  intros Θ i A B X HA HB HX.
  pose proof (wf_sub_id _ (expression_context _ _ _ HA)) as Hid.
  pose proof (wf_sub_compose _ _ _ _ _ Hid Hid) as HII.
  pose proof (wf_sub_eq_id_compose_right _ _ _ Hid) as HId.
  pose proof (substitute_type _ _ _ _ _ HII HA) as HAT.
  assert (HE : wf_exp_eq Θ (a_typ i) A (a_sub A (a_compose a_id a_id))).
  { apply wf_exp_eq_sym; eapply wf_exp_eq_trans;
      [eapply substitute_type_equality; [exact HII | exact HId | now apply reflexive_expression]
      | now apply type_substitution_identity]. }
  pose proof (convert_expression _ _ _ _ _ HX HAT HE) as Hx.
  split; [exact Hx |].
  exact (type_extension_congruence _ _ _ _ _ _ _ _ _ _ HII HA HB HId Hx (reflexive_expression _ _ _ Hx)).
Qed.

Lemma apply_glued_value : forall U Θ i A B a ρ C R T M m X x S,
    universe_invariants U -> universe_coherence U ->
    glued_type U Θ i A a R ->
    wf_exp (A :: Θ) (a_typ i) B ->
    at_type i (d_pi a ρ C) (d_pi a ρ C) S ->
    family_closes Θ ρ C R -> family_glues U Θ i B ρ C R T ->
    glued_term U Θ (a_pi A B) M (d_pi a ρ C) m ->
    glued_term U Θ A X a x ->
    exists b y, eval_exp C (extend_env ρ x) b /\ eval_app m x y /\      glued_term U Θ (a_sub B (a_extend a_id X)) (a_app M X) b y.
Proof.
  intros U Θ i A B a ρ C R T M m X x S HU HC GA HB Hsem HF HT HM HX.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HA.
  pose proof (glued_type_pi _ _ _ _ _ _ _ _ _ _ _ Hsem GA HB HF HT) as GP.
  pose proof (candidate_at_identity _ _ _ _ _ _ _ _ HU HC GP HM) as (_ & _ & _ & Hcall).
  pose proof (candidate_at_identity _ _ _ _ _ _ _ _ HU HC GA HX) as HR.
  pose proof (weakening_identity _ (expression_context _ _ _ HA)) as Hid.
  pose proof (weakening_compose _ _ _ _ _ Hid Hid) as HII.
  pose proof (reindex_candidate _ _ _ _ _ _ _ _ _ _ _ HU HC GA Hid HII HR) as HR'.
  destruct (Hcall _ _ _ _ Hid HR') as (b & y & Hb & Hy & Hval).
  pose proof (HT _ _ _ _ HII HR' _ Hb) as GB.
  pose proof (glued_term_typing _ _ _ _ _ _ HX) as HXw.
  pose proof (glued_term_typing _ _ _ _ _ _ HM) as HMw.
  destruct (instantiated_identity_compose _ _ _ _ _ HA HB HXw) as (_ & HE).
  pose proof (substitute_type _ _ _ _ _ (instantiate_type _ _ _ _ HA HXw) HB) as HBT.
  exists b, y; split; [exact Hb |]. split; [exact Hy |].
  eapply glued_term_expression_change; [exact HU|exact HC| |exact (wf_app _ _ _ _ _ _ HA HB HMw HXw)|].
  - eapply glued_term_type_change; [exact (glued_at_candidate_identity _ _ _ _ _ _ _ _ GB Hval)|exact HBT|exact HE].
  - exact (wf_exp_eq_app_cong _ _ _ _ _ _ _ _ HA HB (wf_exp_eq_sub_id _ _ _ HMw) (reflexive_expression _ _ _ HXw)).
Qed.

Lemma gluing_application : forall k Γ i A B M N,
    i < k ->
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    wf_exp Γ (a_pi A B) M -> wf_exp Γ A N ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (a_typ i) B ->
    typing_respects_gluing (gluing_universes k) Γ (a_pi A B) M ->
    typing_respects_gluing (gluing_universes k) Γ A N ->
    typing_respects_gluing (gluing_universes k) Γ (a_sub B (a_extend a_id N)) (a_app M N).
Proof.
  intros k Γ i A B M N Hk HA HB HM HN HAg HBg HMg HNg Θ σ ρ HE.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  destruct (extract_glued_code _ _ _ _ _ _ _ Hk HE HAg) as (a & R & Hae & GA).
  destruct (construct_glued_family _ _ _ _ _ _ _ _ _ _ Hk HE HA HB Hae GA HBg) as (T & HF & HT).
  destruct (HMg _ _ _ HE) as (c & m & Hc & Hm & GM).
  destruct (HNg _ _ _ HE) as (d & n & Hd & Hn & GN).
  assert (Hpi : eval_exp (a_pi A B) ρ (d_pi a ρ B)) by now apply eval_exp_pi.
  pose proof (exp_unique _ _ _ Hc _ Hpi) as E; subst c.
  pose proof (exp_unique _ _ _ Hd _ Hae) as E; subst d.
  pose proof (wf_pi _ _ _ _ HA HB) as HpiT.
  destruct (semantically_typed_code _ _ _ _ _ HpiT (glued_environment_semantic _ _ _ _ _ HE) Hpi) as (S & Hsem).
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HS HA) HB) as HBs.
  pose proof (wf_pi _ _ _ _ HAs HBs) as HNative.
  pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB) as HpiE.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GM HNative HpiE) as GM'.
  destruct (apply_glued_value _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    HU HC GA HBs Hsem HF HT GM' GN) as (b & y & Hb & Hy & HG).
  pose proof (wf_exp_sub _ _ _ _ _ HS HN) as HNs.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HNs) as Hinst.
  pose proof (substitute_type _ _ _ _ _ Hinst HB) as HBT.
  pose proof (substitute_into_lift _ _ _ _ _ _ _ _ HS HA HB HNs) as HBE.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ HG HBT HBE) as Hout.
  pose proof (substitute_type _ _ _ _ _ HS (substitute_type _ _ _ _ _ (instantiate_type _ _ _ _ HA HN) HB)) as Hraw.
  pose proof (substitute_instantiated_type _ _ _ _ _ _ _ _ HS HA HB HN) as HrawE.
  exists b, y; split.
  - eapply eval_exp_sub; [eapply eval_sub_extend; [apply eval_sub_id|exact Hn] | exact Hb].
  - split; [eapply eval_exp_app; eassumption |].
    eapply glued_term_type_change; [|exact Hraw|exact (wf_exp_eq_sym _ _ _ _ HrawE)].
    eapply glued_term_expression_change; [exact HU|exact HC|exact Hout| |].
    + eapply convert_expression.
      * exact (wf_exp_sub _ _ _ _ _ HS (wf_app _ _ _ _ _ _ HA HB HM HN)).
      * exact HBT.
      * exact HrawE.
    + apply wf_exp_eq_sym; exact (wf_exp_eq_app_sub _ _ _ _ _ _ _ _ HS HA HB HM HN).
Qed.

Lemma semantically_typed_value : forall Γ A M ρ a m,
    wf_exp Γ A M -> env_related Γ ρ ρ ->
    eval_exp A ρ a -> eval_exp M ρ m -> semantic_member a m.
Proof.
  intros Γ A M ρ a m HT HE Hae Hme.
  destruct fundamental_evaluation as (_ & _ & H & _).
  destruct (proj1 (H _ _ _ HT) _ _ HE)
    as (R & (a' & b' & HA & HB & i & HR) & m' & n' & HM & HN & Hmem).
  resolve_eval; exists i,R; auto.
Qed.

Lemma gluing_convert_type_at_environment : forall U Γ A B j,
    universe_invariants U -> universe_coherence U ->
    wf_exp Γ (a_typ j) B -> wf_exp_eq Γ (a_typ j) A B ->
    forall Θ σ ρ M a m,
      glued_environment U Θ Γ σ ρ -> eval_exp A ρ a ->
      glued_term U Θ (a_sub A σ) M a m ->
      exists b, eval_exp B ρ b /\ glued_term U Θ (a_sub B σ) M b m.
Proof.
  intros U Γ A B j HU HC HB HE Θ σ ρ M a m HEnv HA HG.
  destruct fundamental_evaluation as (_ & _ & _ & Heq & _).
  destruct (from_universe _ _ _ _ _ (proj1 (Heq _ _ _ _ HE) _ _
      (glued_environment_semantic _ _ _ _ _ HEnv))) as (a' & b & Ha' & Hb & V & HV).
  pose proof (exp_unique _ _ _ Ha' _ HA) as E; subst a'.
  pose proof (glued_environment_typing _ _ _ _ _ HEnv) as HS.
  pose proof (substitute_type _ _ _ _ _ HS HB) as HBs.
  assert (Hty : wf_exp_eq Θ (a_typ j) (a_sub A σ) (a_sub B σ)).
  { eapply substitute_type_equality; [exact HS | now apply reflexive_substitution | exact HE]. }
  pose proof (glued_term_typing _ _ _ _ _ _ HG) as HMw.
  pose proof (convert_expression _ _ _ _ _ HMw HBs Hty) as HM'.
  destruct HG as (i & R & HGT & HMg).
  pose proof (weakening_identity _ (expression_context _ _ _ HMw)) as Hid.
  destruct (candidate_has_invariants _ _ _ _ _ _ HGT _ _ _ _ Hid HMg) as (_ & (k & T & HT & Hrel) & _).
  assert (HV' : V m m).
  { exact (proj2 (at_type_coherent_l _ _ _ _ _ _ _ HV HT _ _) Hrel). }
  exists b; split; [exact Hb |].
  eapply glued_term_change;
    [exact HU | exact HC | exists i, R; exact (conj HGT HMg) | exact HBs | exact Hty
    | exact HM' | now apply reflexive_expression | exact HV | exact HV'].
Qed.

Lemma gluing_convert_type : forall U Γ A B M j,
    universe_invariants U -> universe_coherence U ->
    wf_exp Γ (a_typ j) B -> wf_exp_eq Γ (a_typ j) A B ->
    typing_respects_gluing U Γ A M ->
    typing_respects_gluing U Γ B M.
Proof.
  intros U Γ A B M j HU HC HB HE HM Θ σ ρ HEnv.
  destruct (HM _ _ _ HEnv) as (a & m & HA & He & HG).
  destruct (gluing_convert_type_at_environment _ _ _ _ _ HU HC HB HE _ _ _ _ _ _ HEnv HA HG)
    as (b & Hb & Hterm).
  exists b, m; tauto.
Qed.

Lemma gluing_cumulativity : forall k Γ i j A,
    i <= j -> j < k ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ j) A.
Proof.
  intros k Γ i j A Hle Hk HA Θ σ ρ HE.
  destruct (extract_glued_code k Γ Θ σ ρ i A ltac:(lia) HE HA) as (a & R & Ha & HR).
  exists (d_univ j), a; split; [apply eval_exp_typ |]. split; [exact Ha |].
  eapply gluing_code_at_substitution; [exact Hk | exact (glued_environment_typing _ _ _ _ _ HE) |].
  eapply glued_type_cumulative; [exact HR | exact Hle].
Qed.

Lemma gluing_type_substitution : forall U Γ Δ σ i A,
    universe_invariants U -> universe_coherence U ->
    wf_sub Γ Δ σ -> wf_exp Δ (a_typ i) A ->
    substitution_respects_gluing U Γ Δ σ ->
    typing_respects_gluing U Δ (a_typ i) A ->
    typing_respects_gluing U Γ (a_typ i) (a_sub A σ).
Proof.
  intros U Γ Δ σ i A HU HC HS HA Hg HAg.
  eapply gluing_convert_type;
    [exact HU | exact HC | apply wf_typ; exact (proj1 (substitution_contexts _ _ _ HS)) | exact (wf_exp_eq_typ_sub _ _ _ _ HS) |].
  eapply gluing_exp_sub; eassumption.
Qed.

Lemma gluing_instantiation : forall U Γ i A X,
    universe_invariants U -> universe_coherence U ->
    wf_exp Γ (a_typ i) A -> wf_exp Γ A X -> typing_respects_gluing U Γ A X ->
    substitution_respects_gluing U Γ (A :: Γ) (a_extend a_id X).
Proof.
  intros U Γ i A X HU HC HA HX HG.
  pose proof (expression_context _ _ _ HA) as HGamma.
  pose proof (wf_sub_id _ HGamma) as Hid.
  pose proof (substitute_type _ _ _ _ _ Hid HA) as HAt.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_identity _ _ _ HA)) as HAE.
  eapply gluing_sub_extend; [exact HU | exact HC | exact Hid | exact HA
     | exact (convert_expression _ _ _ _ _ HX HAt HAE)
     | exact (gluing_sub_id _ _ HU HC) |].
  eapply gluing_convert_type; eassumption.
Qed.

Definition function_action_on_neutrals Γ A B a ρ C M m :=
  forall Δ σ X n, weakening Δ Γ σ ->
    wf_exp Δ (a_sub A σ) X ->
    neutral_under_weakening Δ (a_sub A σ) X n ->
    exists b y,
      eval_exp C (extend_env ρ (d_neut a n)) b /\ eval_app m (d_neut a n) y /\
      quoted_term Δ (a_sub B (a_extend σ X)) (a_app (a_sub M σ) X) b y.

Lemma quote_function_action_on_neutrals : forall Γ i A B a ρ C M m,
    quotation_type Γ i A a ->
    wf_exp (A :: Γ) (a_typ i) B ->
    wf_exp Γ (a_pi A B) M ->
    function_action_on_neutrals Γ A B a ρ C M m ->
    term_under_weakening Γ (a_pi A B) M (d_pi a ρ C) m.
Proof.
  intros Γ i A B a ρ C M m HQ HB HM Hact Δ σ HW.
  pose proof (quotation_well_formed _ _ _ _ HQ) as HA.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  pose proof (proj1 (substitution_contexts _ _ _ HS)) as HD.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (wf_ctx_extend _ _ _ HD HAs) as HDb.
  pose proof (wf_sub_weaken _ _ HDb) as Hwk.
  pose proof (lift_substitution _ _ _ _ _ HS HA) as HQS.
  pose proof (substitute_type _ _ _ _ _ HQS HB) as HBs.
  pose proof (wf_pi _ _ _ _ HA HB) as HP.
  pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB) as HE.
  pose proof (wf_pi _ _ _ _ HAs HBs) as Hdirect.
  pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HMs.
  pose proof (convert_expression _ _ _ _ _ HMs Hdirect HE) as HMd.
  destruct (fresh_argument_quotation _ _ _ _ _ _ HQ HW) as (HT & HX & HXN & HXQ).
  destruct (Hact _ _ _ _ HT HX HXN) as (b & y & HBe & Happly & Hbody).
  pose proof (weakening_is_typed _ _ _ HT) as HTsub.
  pose proof (substitute_type _ _ _ _ _ HTsub HA) as HAt.
  pose proof (lift_substitution _ _ _ _ _ HTsub HA) as HQt.
  pose proof (substitute_type _ _ _ _ _ HQt HB) as HBt.
  assert (Htyped : wf_exp_eq (a_sub A σ :: Δ)
    (a_pi (a_sub A (a_compose σ a_weaken)) (a_sub B (Syntax.q (a_compose σ a_weaken))))
    (a_sub (a_sub M σ) a_weaken) (a_sub M (a_compose σ a_weaken))).
  {
    eapply convert_equality.
    - apply wf_exp_eq_sym; eapply wf_exp_eq_sub_compose; eassumption.
    - eapply wf_pi; eassumption.
    - eapply wf_exp_eq_pi_sub; eassumption.
  }
  assert (HbodyE : wf_exp_eq (a_sub A σ :: Δ) (a_sub B (Syntax.q σ))
    (a_app (a_sub (a_sub M σ) a_weaken) (a_var 0)) (a_app (a_sub M (a_compose σ a_weaken)) (a_var 0))).
  {
    eapply convert_equality.
    - exact (wf_exp_eq_app_cong _ _ _ _ _ _ _ _ HAt HBt Htyped (reflexive_expression _ _ _ HX)).
    - exact HBs.
    - exact (substitute_into_lift _ _ _ _ _ _ _ _ HTsub HA HB HX).
  }
  eapply quote_term_type_conversion.
  - exact (substitute_type _ _ _ _ _ HS HP).
  - exact (wf_exp_eq_sym _ _ _ _ HE).
  - eapply quote_term_pi; [exact HAs | exact HBs | exact HMd | | exact Happly | exact HBe |].
    + exact (quotation_of_type _ _ _ _ HQ _ _ HW).
    + eapply quote_term_conversion; [exact HbodyE | exact Hbody].
Qed.



Lemma finish_glued_function : forall U Θ i A B a ρ C R T S M m,
    universe_invariants U -> universe_coherence U ->
    glued_type U Θ i A a R -> wf_exp (A :: Θ) (a_typ i) B ->
    at_type i (d_pi a ρ C) (d_pi a ρ C) S ->
    family_closes Θ ρ C R -> family_glues U Θ i B ρ C R T ->
    wf_exp Θ (a_pi A B) M -> semantic_member (d_pi a ρ C) m ->
    callable R T Θ A B ρ C Θ a_id M m ->
    glued_term U Θ (a_pi A B) M (d_pi a ρ C) m.
Proof.
  intros U Θ i A B a ρ C R T S M m HU HC GA HB Hsem HF HT HM Hm Hcall.
  destruct (quoted_candidate_reflects _ _ _ _ _ _ HU GA) as (HQA & HRA).
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HA.
  pose proof (glued_type_pi _ _ _ _ _ _ _ _ _ _ _ Hsem GA HB HF HT) as GP.
  eapply glued_at_candidate_identity; [exact GP |].
  pose proof (wf_pi _ _ _ _ HA HB) as HP.
  destruct (preserve_at_id _ _ _ _ _ HP HM (reflexive_expression _ _ _ HM)) as (HMi & _).
  split; [exact HMi |]. split; [exact Hm |]. split; [|exact Hcall].
  pose proof (expression_context _ _ _ HM) as HG.
  pose proof (wf_sub_id _ HG) as HI.
  eapply convert_term_under_weakening.
  - exact (substitute_type _ _ _ _ _ HI HP).
  - apply wf_exp_eq_sym; now apply type_substitution_identity.
  - eapply quote_function_action_on_neutrals; [exact HQA | exact HB | exact HM |].
    intros Ξ τ X p HW HX HN.
    pose proof (weakening_identity _ HG) as Hid.
    pose proof (weakening_compose _ _ _ _ _ HW Hid) as Hcomp.
    pose proof (HRA _ _ _ _ HW HX HN) as HK.
    pose proof (reindex_candidate _ _ _ _ _ _ _ _ _ _ _ HU HC GA HW Hcomp HK) as HK'.
    destruct (Hcall _ _ _ _ HW HK') as (b & y & Hb & Hy & Hry).
    pose proof (HT _ _ _ _ Hcomp HK' _ Hb) as HGB.
    pose proof (glued_at_candidate_identity _ _ _ _ _ _ _ _ HGB Hry) as HY.
    pose proof (weakening_is_typed _ _ _ HW) as HS.
    pose proof (weakening_is_typed _ _ _ Hcomp) as HS'.
    pose proof (wf_sub_eq_id_compose_right _ _ _ HS) as HSE.
    destruct (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ Hcomp HK') as (HX' & _).
    pose proof (type_extension_congruence _ _ _ _ _ _ _ _ _ _ HS' HA HB HSE HX' (reflexive_expression _ _ _ HX')) as HBE.
    exists b, y; split; [exact Hb |]. split; [exact Hy |].
    eapply quote_term_type_conversion;
      [exact (substitute_type _ _ _ _ _ (wf_sub_extend _ _ _ _ _ _ HS HA HX) HB)
      | exact HBE | exact (glued_term_quote _ _ _ _ _ _ HY)].
Qed.

Lemma glued_family_identity : forall U Θ i A B a ρ C R T Ξ τ X x b Y y,
    universe_invariants U -> universe_coherence U ->
    glued_type U Θ i A a R -> wf_exp (A :: Θ) (a_typ i) B ->
    family_glues U Θ i B ρ C R T ->
    weakening Ξ Θ τ ->
    R Ξ (a_compose a_id τ) X x ->
    eval_exp C (extend_env ρ x) b ->
    glued_term U Ξ (a_sub B (a_extend τ X)) Y b y ->
    T Ξ (a_compose a_id τ) X x Ξ a_id Y y.
Proof.
  intros U Θ i A B a ρ C R T Ξ τ X x b Y y HU HC GA HB HT HW HX Hb HY.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HA.
  pose proof (weakening_identity _ (expression_context _ _ _ HA)) as HI.
  pose proof (weakening_compose _ _ _ _ _ HW HI) as Ht.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  pose proof (weakening_is_typed _ _ _ Ht) as HS'.
  destruct (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ Ht HX) as (HXw & _).
  pose proof (type_extension_congruence _ _ _ _ _ _ _ _ _ _ HS' HA HB
    (wf_sub_eq_id_compose_right _ _ _ HS) HXw (reflexive_expression _ _ _ HXw)) as HE.
  pose proof (HT _ _ _ _ Ht HX _ Hb) as GB.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GB) as HBT.
  eapply candidate_at_identity; [exact HU | exact HC | exact GB |].
  eapply glued_term_type_change; [exact HY | exact HBT | exact (wf_exp_eq_sym _ _ _ _ HE)].
Qed.

Lemma lambda_beta_under_substitution : forall Γ Θ σ i A B M X,
    wf_sub Θ Γ σ ->
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    wf_exp (A :: Γ) B M ->
    wf_exp Θ (a_sub A σ) X ->
    wf_exp_eq Θ (a_sub B (a_extend σ X))
      (a_app (a_sub (a_fn A M) σ) X) (a_sub M (a_extend σ X)).
Proof.
  intros Γ Θ σ i A B M X HS HA HB HM HX.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (lift_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (substitute_type _ _ _ _ _ HQ HB) as HBs.
  pose proof (wf_exp_sub _ _ _ _ _ HQ HM) as HMs.
  pose proof (wf_exp_eq_fn_sub _ _ _ _ _ _ _ HS HA HM) as HFn.
  pose proof (convert_equality _ _ _ _ _ _ HFn (wf_pi _ _ _ _ HAs HBs)
    (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB)) as HFn'.
  pose proof (wf_exp_eq_app_cong _ _ _ _ _ _ _ _ HAs HBs HFn' (reflexive_expression _ _ _ HX)) as HC.
  pose proof (wf_exp_eq_pi_beta _ _ _ _ _ _ HAs HBs HMs HX) as HBeta.
  pose proof (substitute_type _ _ _ _ _ (wf_sub_extend _ _ _ _ _ _ HS HA HX) HB) as HBT.
  pose proof (substitute_into_lift _ _ _ _ _ _ _ _ HS HA HB HX) as HIE.
  eapply wf_exp_eq_trans; [exact (convert_equality _ _ _ _ _ _ HC HBT HIE) |].
  eapply wf_exp_eq_trans; [exact (convert_equality _ _ _ _ _ _ HBeta HBT HIE) |].
  pose proof (wf_sub_id _ (expression_context _ _ _ HX)) as Hid.
  pose proof (wf_sub_compose _ _ _ _ _ Hid HS) as HSS.
  pose proof (wf_sub_eq_id_compose_left _ _ _ HS) as HSE.
  pose proof (substitute_type _ _ _ _ _ HSS HA) as HA'.
  assert (HE : wf_exp_eq Θ (a_typ i) (a_sub A (a_compose σ a_id)) (a_sub A σ)).
  { eapply substitute_type_equality; [exact HSS | exact HSE | now apply reflexive_expression]. }
  pose proof (convert_expression _ _ _ _ _ HX HA' (wf_exp_eq_sym _ _ _ _ HE)) as HX'.
  pose proof (type_extension_congruence _ _ _ _ _ _ _ _ _ _ HSS HA HB HSE HX' (reflexive_expression _ _ _ HX')) as HE'.
  eapply wf_exp_eq_trans.
  - exact (convert_equality _ _ _ _ _ _
      (expression_after_lift_instantiation _ _ _ _ _ _ _ _ _ _ Hid HS HA HX' HM) HBT HE').
  - eapply convert_equality; [|exact HBT |exact HE'].
    eapply wf_exp_eq_sub_cong; [exact (reflexive_expression _ _ _ HM) |].
    eapply wf_sub_eq_extend_cong; [exact HSE | exact HA | now apply reflexive_expression].
Qed.

Lemma gluing_function : forall k Γ i A B M,
    i < k ->
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    wf_exp (A :: Γ) B M ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (a_typ i) B ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) B M ->
    typing_respects_gluing (gluing_universes k) Γ (a_pi A B) (a_fn A M).
Proof.
  intros k Γ i A B M Hk HA HB HM HAg HBg HMg Θ σ ρ HE.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  destruct (extract_glued_code _ _ _ _ _ _ _ Hk HE HAg) as (a & R & Hae & GA).
  destruct (construct_glued_family _ _ _ _ _ _ _ _ _ _ Hk HE HA HB Hae GA HBg) as (T & HF & HT).
  pose proof (wf_pi _ _ _ _ HA HB) as HP.
  assert (HPI : eval_exp (a_pi A B) ρ (d_pi a ρ B)) by now apply eval_exp_pi.
  pose proof (glued_environment_semantic _ _ _ _ _ HE) as Hρ.
  destruct (semantically_typed_code _ _ _ _ _ HP Hρ HPI) as (W & Hsem).
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (lift_substitution _ _ _ _ _ HS HA) as HQ.
  pose proof (substitute_type _ _ _ _ _ HQ HB) as HBs.
  pose proof (wf_exp_sub _ _ _ _ _ HQ HM) as HMs.
  pose proof (wf_fn _ _ _ _ _ HAs HMs) as HFn.
  pose proof (wf_fn _ _ _ _ _ HA HM) as HFnOrig.
  assert (HFunEval : eval_exp (a_fn A M) ρ (d_fn ρ M)) by apply eval_exp_fn.
  pose proof (semantically_typed_value _ _ _ _ _ _ HFnOrig Hρ HPI HFunEval) as Hmem.
  assert (Hcall : callable R T Θ (a_sub A σ) (a_sub B (Syntax.q σ)) ρ B
     Θ a_id (a_fn (a_sub A σ) (a_sub M (Syntax.q σ))) (d_fn ρ M)).
  {
    intros Ξ τ X x HW HX.
    pose proof (weakening_identity _ (expression_context _ _ _ HAs)) as Hid.
    pose proof (weakening_compose _ _ _ _ _ HW Hid) as Hcomp.
    pose proof (reindex_candidate _ _ _ _ _ _ _ _ _ _ _ HU HC GA Hcomp HW HX) as HX'.
    pose proof (candidate_to_world _ _ _ _ _ _ _ _ _ _ HU HC GA HW HX') as HXg.
    pose proof (weakening_is_typed _ _ _ HW) as HTau.
    pose proof (wf_sub_compose _ _ _ _ _ HTau HS) as HST.
    pose proof (substitute_type _ _ _ _ _ HST HA) as HASt.
    pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_compose _ _ _ _ _ _ _ HTau HS HA)) as HAE.
    pose proof (glued_term_type_change _ _ _ _ _ _ _ _ HXg HASt HAE) as HXg'.
    pose proof (instantiate_glued_environment _ _ _ _ _ _ _ _ _ _ _ _
      HU HC (gluing_universes_weaken k) HE HW HA Hae HXg') as HEnv.
    destruct (HMg _ _ _ HEnv) as (b & y & Hb & Hy & HG).
    pose proof (glued_term_typing _ _ _ _ _ _ HXg') as HXt.
    pose proof (glued_term_typing _ _ _ _ _ _ HXg) as HXw.
    destruct (typed_lift_instantiation _ _ _ _ _ _ _ _ HTau HS HA HXt) as (HExt & HEq).
    pose proof (substitute_type _ _ _ _ _ HExt HBs) as HBT.
    pose proof (type_after_lift_instantiation _ _ _ _ _ _ _ _ _ _ HTau HS HA HXt HB) as HBE.
    pose proof (expression_after_lift_instantiation _ _ _ _ _ _ _ _ _ _ HTau HS HA HXt HM) as HBody.
    pose proof (lambda_beta_under_substitution _ _ _ _ _ _ _ _ HTau HAs HBs HMs HXw) as HBeta.
    exists b, y; split; [exact Hb |]. split; [now apply eval_app_fn |].
    eapply glued_family_identity; [exact HU | exact HC | exact GA | exact HBs | exact HT | exact HW | exact HX | exact Hb |].
    eapply glued_term_expression_change; [exact HU | exact HC | | |].
    - exact (glued_term_type_change _ _ _ _ _ _ _ _ HG HBT (wf_exp_eq_sym _ _ _ _ HBE)).
    - eapply convert_expression.
      + eapply wf_app;
          [exact (substitute_type _ _ _ _ _ HTau HAs)
          | exact (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HTau HAs) HBs)
          | | exact HXw].
        eapply convert_expression;
          [exact (wf_exp_sub _ _ _ _ _ HTau HFn) | | exact (wf_exp_eq_pi_sub _ _ _ _ _ _ HTau HAs HBs)].
        eapply wf_pi; eapply substitute_type; eauto using lift_substitution.
      + exact HBT.
      + exact (substitute_into_lift _ _ _ _ _ _ _ _ HTau HAs HBs HXw).
    - apply wf_exp_eq_sym; eapply wf_exp_eq_trans; [exact HBeta |].
      eapply convert_equality; [exact HBody | exact HBT | exact (wf_exp_eq_sym _ _ _ _ HBE)].
  }
  pose proof (finish_glued_function _ _ _ _ _ _ _ _ _ _ _ _ _
    HU HC GA HBs Hsem HF HT HFn Hmem Hcall) as GFn.
  pose proof (substitute_type _ _ _ _ _ HS HP) as HPs.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB)) as HPeq.
  exists (d_pi a ρ B), (d_fn ρ M); split; [exact HPI |]. split; [exact HFunEval |].
  eapply glued_term_expression_change;
    [exact HU | exact HC | exact (glued_term_type_change _ _ _ _ _ _ _ _ GFn HPs HPeq)
    |exact (wf_exp_sub _ _ _ _ _ HS HFnOrig) |].
  apply wf_exp_eq_sym; exact (wf_exp_eq_fn_sub _ _ _ _ _ _ _ HS HA HM).
Qed.

Lemma glued_term_at_weakening : forall U Θ i A a R M m,
    universe_invariants U -> universe_coherence U -> universe_weakening U ->
    glued_type U Θ i A a R -> glued_term U Θ A M a m ->
    forall Ξ τ, weakening Ξ Θ τ -> R Ξ τ (a_sub M τ) m.
Proof.
  intros U Θ i A a R M m HU HC HW GA GM Ξ τ Hτ.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HA.
  pose proof (weakening_identity _ (expression_context _ _ _ HA)) as Hid.
  pose proof (weakening_compose _ _ _ _ _ Hτ Hid) as Hcomp.
  eapply reindex_candidate; [exact HU | exact HC | exact GA | exact Hcomp | exact Hτ |].
  eapply candidates_weaken; [exact HU | exact HC | exact HW | exact GA | exact Hid | exact Hτ |].
  exact (candidate_at_identity _ _ _ _ _ _ _ _ HU HC GA GM).
Qed.

Lemma gluing_equality_data : forall k Γ i A X Y Θ σ ρ,
    i < k -> wf_exp Γ (a_typ i) A -> wf_exp Γ A X -> wf_exp Γ A Y ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) Γ A X ->
    typing_respects_gluing (gluing_universes k) Γ A Y ->
    glued_environment (gluing_universes k) Θ Γ σ ρ ->
    exists a x y R S,
      eval_exp A ρ a /\ eval_exp X ρ x /\ eval_exp Y ρ y /\
      at_type i (d_eq a x y) (d_eq a x y) S /\
      glued_type (gluing_universes k) Θ i (a_sub A σ) a R /\
      glued_term (gluing_universes k) Θ (a_sub A σ) (a_sub X σ) a x /\
      glued_term (gluing_universes k) Θ (a_sub A σ) (a_sub Y σ) a y.
Proof.
  intros k Γ i A X Y Θ σ ρ Hk HA HX HY HAg HXg HYg HE.
  destruct (extract_glued_code _ _ _ _ _ _ _ Hk HE HAg) as (a & R & Ha & GA).
  destruct (HXg _ _ _ HE) as (a' & x & Ha' & Hx & GX).
  destruct (HYg _ _ _ HE) as (a'' & y & Ha'' & Hy & GY).
  pose proof (exp_unique _ _ _ Ha' _ Ha) as H1; subst a'.
  pose proof (exp_unique _ _ _ Ha'' _ Ha) as H2; subst a''.
  assert (Hval : eval_exp (a_eq A X Y) ρ (d_eq a x y)) by now apply eval_exp_eq.
  destruct (semantically_typed_code _ _ _ _ _ (wf_eq _ _ _ _ _ HA HX HY)
    (glued_environment_semantic _ _ _ _ _ HE) Hval) as (S & Hsem).
  exists a, x, y, R, S; repeat split; assumption.
Qed.

Lemma gluing_equality : forall k Γ i A X Y,
    i < k -> wf_exp Γ (a_typ i) A -> wf_exp Γ A X -> wf_exp Γ A Y ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) Γ A X ->
    typing_respects_gluing (gluing_universes k) Γ A Y ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) (a_eq A X Y).
Proof.
  intros k Γ i A X Y Hk HA HX HY HAg HXg HYg Θ σ ρ HE.
  destruct (gluing_equality_data _ _ _ _ _ _ _ _ _ Hk HA HX HY HAg HXg HYg HE)
    as (a & x & y & R & S & Ha & Hx & Hy & Hsem & GA & GX & GY).
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (gluing_universes_weaken k) as HW.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (wf_eq _ _ _ _ _ HA HX HY) as HT.
  exists (d_univ i), (d_eq a x y); split; [apply eval_exp_typ |].
  split; [now apply eval_exp_eq |].
  eapply gluing_code_at_substitution; [exact Hk | exact HS |].
  eapply glued_type_convert; [|exact (substitute_type _ _ _ _ _ HS HT) |].
  - eapply glued_type_eq; [exact Hsem | exact GA | exact (wf_exp_sub _ _ _ _ _ HS HX)
      | exact (wf_exp_sub _ _ _ _ _ HS HY) | |].
    + exact (glued_term_at_weakening _ _ _ _ _ _ _ _ HU HC HW GA GX).
    + exact (glued_term_at_weakening _ _ _ _ _ _ _ _ HU HC HW GA GY).
  - apply wf_exp_eq_sym; exact (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HS HA HX HY).
Qed.

Lemma finish_glued_reflexivity : forall U Θ i A X Y a x y R S M Z z,
    universe_invariants U -> universe_coherence U -> universe_weakening U ->
    glued_type U Θ i A a R ->
    wf_exp Θ A X -> wf_exp Θ A Y ->
    (forall Ξ τ, weakening Ξ Θ τ -> R Ξ τ (a_sub X τ) x) ->
    (forall Ξ τ, weakening Ξ Θ τ -> R Ξ τ (a_sub Y τ) y) ->
    at_type i (d_eq a x y) (d_eq a x y) S ->
    wf_exp Θ (a_eq A X Y) M ->
    semantic_member (d_eq a x y) (d_refl z) ->
    R Θ a_id Z z ->
    wf_exp_eq Θ (a_sub A a_id) Z (a_sub X a_id) ->
    wf_exp_eq Θ (a_sub A a_id) Z (a_sub Y a_id) ->
    wf_exp_eq Θ (a_sub (a_eq A X Y) a_id) M (a_refl (a_sub A a_id) Z) ->
    glued_term U Θ (a_eq A X Y) M (d_eq a x y) (d_refl z).
Proof.
  intros U Θ i A X Y a x y R S M Z z HU HC HW GA HX HY HXR HYR Hsem HM HSZ HZ HZX HZY HME.
  pose proof (glued_type_eq _ _ _ _ _ _ _ _ _ _ _ Hsem GA HX HY HXR HYR) as GE.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HA.
  pose proof (expression_context _ _ _ HA) as HΘ.
  pose proof (weakening_identity _ HΘ) as Hid.
  pose proof (wf_eq _ _ _ _ _ HA HX HY) as HEq.
  destruct (preserve_at_id _ _ _ _ _ HEq HM (reflexive_expression _ _ _ HM)) as (HMi & _).
  destruct (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ Hid HZ) as (HZt & _).
  pose proof (proj1 (quoted_candidate_reflects _ _ _ _ _ _ HU GA)) as HQA.
  eapply glued_at_candidate_identity; [exact GE |].
  split; [exact HMi |]. split; [exact HSZ |]. split.
  - intros Ξ τ Hτ.
    pose proof (weakening_is_typed _ _ _ Hτ) as HT.
    pose proof (weakening_compose _ _ _ _ _ Hτ Hid) as Hcomp.
    pose proof (weakening_is_typed _ _ _ Hcomp) as HS.
    destruct (weakened_reflexivity _ _ _ _ _ _ _ _ _ _ _ HA HX HY Hid Hτ HZt HZX HZY HME)
      as (HX' & HY' & HM').
    pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
    pose proof (wf_exp_sub _ _ _ _ _ HS HX) as HXs.
    pose proof (wf_exp_sub _ _ _ _ _ HS HY) as HYs.
    pose proof (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HS HA HX HY) as HEs.
    pose proof (wf_eq _ _ _ _ _ HAs HXs HYs) as Hdirect.
    pose proof (substitute_type _ _ _ _ _ HS HEq) as HcompT.
    eapply quote_term_type_conversion.
    + exact (substitute_type _ _ _ _ _ HT (substitute_type _ _ _ _ _ (wf_sub_id _ HΘ) HEq)).
    + eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact HEs |].
      exact (type_substitution_compose _ _ _ _ _ _ _ HT (wf_sub_id _ HΘ) HEq).
    + eapply quote_term_refl;
        [exact HAs | exact HXs | exact HYs | exact HX' | exact HY' | | exact (quotation_of_type _ _ _ _ HQA _ _ Hcomp) |].
      * exact (convert_equality _ _ _ _ _ _ HM' Hdirect HEs).
      * pose proof (candidates_weaken _ _ _ _ _ _ HU HC HW GA _ _ _ _ _ _ Hid Hτ HZ) as HZ'.
        destruct (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ Hcomp HZ') as (HZt' & _ & HZq).
        exact (observe_term _ _ _ _ _ HZt' HZq).
  - right. exists Z, z; repeat split; try reflexivity; assumption.
Qed.

Lemma gluing_reflexivity : forall k Γ i A M,
    i < k -> wf_exp Γ (a_typ i) A -> wf_exp Γ A M ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) Γ A M ->
    typing_respects_gluing (gluing_universes k) Γ (a_eq A M M) (a_refl A M).
Proof.
  intros k Γ i A M Hk HA HM HAg HMg Θ σ ρ HE.
  destruct (gluing_equality_data _ _ _ _ _ _ _ _ _ Hk HA HM HM HAg HMg HMg HE)
    as (a & x & y & R & S & Ha & Hx & Hy & Hsem & GA & GX & GY).
  pose proof (exp_unique _ _ _ Hx _ Hy) as Hxy; subst y.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (gluing_universes_weaken k) as HW.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HXs.
  pose proof (wf_eq _ _ _ _ _ HAs HXs HXs) as HEq.
  pose proof (wf_refl _ _ _ _ HAs HXs) as HRefl.
  pose proof (wf_refl _ _ _ _ HA HM) as HOrig.
  assert (HEvalT : eval_exp (a_eq A M M) ρ (d_eq a x x)) by now apply eval_exp_eq.
  assert (HEvalM : eval_exp (a_refl A M) ρ (d_refl x)) by now apply eval_exp_refl.
  pose proof (semantically_typed_value _ _ _ _ _ _ HOrig
    (glued_environment_semantic _ _ _ _ _ HE) HEvalT HEvalM) as Hmem.
  pose proof (expression_context _ _ _ HAs) as HΘ.
  pose proof (wf_sub_id _ HΘ) as HI.
  pose proof (weakening_identity _ HΘ) as HID.
  pose proof (glued_term_at_weakening _ _ _ _ _ _ _ _ HU HC HW GA GX) as HXR.
  assert (Hre : wf_exp_eq Θ (a_sub (a_eq (a_sub A σ) (a_sub M σ) (a_sub M σ)) a_id)
    (a_refl (a_sub A σ) (a_sub M σ)) (a_refl (a_sub (a_sub A σ) a_id) (a_sub (a_sub M σ) a_id))).
  {
    eapply wf_exp_eq_trans; [|exact (wf_exp_eq_refl_sub _ _ _ _ _ _ HI HAs HXs)].
    eapply convert_equality; [apply wf_exp_eq_sym; exact (wf_exp_eq_sub_id _ _ _ HRefl)
      | exact (substitute_type _ _ _ _ _ HI HEq) | ].
    apply wf_exp_eq_sym; now apply type_substitution_identity.
  }
  pose proof (finish_glued_reflexivity _ _ _ _ _ _ _ _ _ _ _ _ _ _ HU HC HW GA HXs HXs
    HXR HXR Hsem HRefl Hmem (HXR _ _ HID)
    (reflexive_expression _ _ _ (wf_exp_sub _ _ _ _ _ HI HXs))
    (reflexive_expression _ _ _ (wf_exp_sub _ _ _ _ _ HI HXs)) Hre) as GR.
  pose proof (substitute_type _ _ _ _ _ HS (wf_eq _ _ _ _ _ HA HM HM)) as HT.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HS HA HM HM)) as HTE.
  exists (d_eq a x x), (d_refl x); split; [exact HEvalT |]. split; [exact HEvalM |].
  eapply glued_term_expression_change;
    [exact HU | exact HC | exact (glued_term_type_change _ _ _ _ _ _ _ _ GR HT HTE)
    | exact (wf_exp_sub _ _ _ _ _ HS HOrig) |].
  apply wf_exp_eq_sym; exact (wf_exp_eq_refl_sub _ _ _ _ _ _ HS HA HM).
Qed.

Definition initial_environment_respects_gluing U Γ :=
  exists ρ, initial_env Γ ρ /\ glued_environment U Γ Γ a_id ρ.

Lemma initial_environment_empty : forall U, initial_environment_respects_gluing U nil.
Proof.
  intros U; exists empty_env; split; [apply initial_env_nil |].
  apply glued_environment_empty, wf_sub_id, wf_ctx_empty.
Qed.

Lemma initial_environment_extend : forall k Γ i A,
    i < k -> wf_exp Γ (a_typ i) A ->
    initial_environment_respects_gluing (gluing_universes k) Γ ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    initial_environment_respects_gluing (gluing_universes k) (A :: Γ).
Proof.
  intros k Γ i A Hk HA (ρ & Hi & Hg) HAg.
  destruct (extract_glued_code _ _ _ _ _ _ _ Hk Hg HAg) as (a & R & Hv & GA).
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (gluing_universes_weaken k) as HW.
  pose proof (expression_context _ _ _ HA) as HΓ.
  pose proof (wf_ctx_extend _ _ _ HΓ HA) as Hext.
  pose proof (weakening_drop _ _ Hext) as Hwk.
  pose proof (weakening_is_typed _ _ _ Hwk) as HwkT.
  pose proof (wf_sub_id _ Hext) as HID.
  pose proof (wf_sub_compose _ _ _ _ _ HID HwkT) as HWI.
  pose proof (wf_sub_compose _ _ _ _ _ HwkT (wf_sub_id _ HΓ)) as HIW.
  pose proof (glued_environment_weaken _ _ _ _ _ HU HC HW Hg _ _ Hwk) as Htail.
  pose proof (glued_type_convert _ _ _ _ _ _ _ GA HA (type_substitution_identity _ _ _ HA)) as Gbase.
  pose proof (glued_type_shift _ _ _ _ _ _ _ _ Gbase Hwk) as Gvar.
  pose proof (type_of_first_variable _ _ Hext) as Hvar.
  pose proof (variable_neutral_under_weakening _ _ _ Hext (here A Γ)) as HN.
  cbn [length Nat.sub] in HN; rewrite Nat.sub_0_r in HN.
  pose proof (reflect_glued_term _ _ _ _ _ _ _ _ HU Gvar Hvar HN) as Gx.
  pose proof (wf_exp_sub _ _ _ _ _ HID Hvar) as Hxi.
  pose proof (substitute_type _ _ _ _ _ HWI HA) as Hty.
  assert (Htye : wf_exp_eq (A :: Γ) (a_typ i) (a_sub A a_weaken) (a_sub A (a_compose a_weaken a_id))).
  { apply wf_exp_eq_sym; eapply substitute_type_equality;
      [exact HWI | exact (wf_sub_eq_id_compose_left _ _ _ HwkT) | now apply reflexive_expression]. }
  pose proof (type_substitution_compose _ _ _ _ _ _ _ HID HwkT HA) as Hcmp.
  exists (extend_env ρ (d_neut a (d_var (length Γ)))); split.
  - now apply initial_env_cons.
  - eapply glued_environment_cons; [exact HID | exact HA | | | |].
    + cbn [drop_env extend_env].
      eapply glued_environment_conversion; [exact HU | exact HC | exact Htail | exact HWI |].
      eapply wf_sub_eq_trans; [exact (wf_sub_eq_id_compose_right _ _ _ HwkT) |].
      apply wf_sub_eq_sym; exact (wf_sub_eq_id_compose_left _ _ _ HwkT).
    + exact Hv.
    + cbn [extend_env].
      eapply glued_term_expression_change;
        [exact HU | exact HC | exact (glued_term_type_change _ _ _ _ _ _ _ _ Gx Hty Htye) | |].
      * exact (convert_expression _ _ _ _ _ Hxi Hty (wf_exp_eq_sym _ _ _ _ Hcmp)).
      * eapply convert_equality;
          [apply wf_exp_eq_sym; exact (wf_exp_eq_sub_id _ _ _ Hvar) | exact Hty | exact Htye].
    + reflexivity.
Qed.

Lemma gluing_implies_soundness : forall U Γ A M,
    universe_invariants U -> universe_coherence U ->
    wf_exp Γ A M ->
    initial_environment_respects_gluing U Γ ->
    typing_respects_gluing U Γ A M ->
    exists W, nbe Γ M A W /\ wf_exp_eq Γ A M W.
Proof.
  intros U Γ A M HU HC HM (ρ & Hi & Hg) Hm.
  destruct (Hm _ _ _ Hg) as (a & m & Ha & Hval & GM).
  destruct (expression_type _ _ _ HM) as (i & HA).
  pose proof (type_substitution_identity _ _ _ HA) as HE.
  eapply glued_readback_soundness; [exact Hi | exact Ha | exact Hval |].
  eapply glued_term_expression_change;
    [exact HU | exact HC | exact (glued_term_type_change _ _ _ _ _ _ _ _ GM HA HE) | exact HM |].
  exact (wf_exp_eq_sub_id _ _ _ HM).
Qed.

Lemma quote_pair_action_on_neutrals : forall Γ i A B a ρ C M m,
    quotation_type Γ i A a ->
    wf_exp (A :: Γ) (a_typ i) B ->
    neutral_dependent_quotation Γ i A B a ρ C ->
    wf_exp Γ (a_sigma A B) M ->
    pair_action Γ A B a ρ C M m ->
    term_under_weakening Γ (a_sigma A B) M (d_sigma a ρ C) m.
Proof.
  intros Γ i A B a ρ C M m HQ HB HC HM Hact Δ σ HW.
  pose proof (quotation_well_formed _ _ _ _ HQ) as HA.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (lift_substitution _ _ _ _ _ HS HA) as HQS.
  pose proof (substitute_type _ _ _ _ _ HQS HB) as HBs.
  pose proof (wf_sigma _ _ _ _ HA HB) as HP.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as HE.
  pose proof (wf_sigma _ _ _ _ HAs HBs) as Hdirect.
  pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HMs.
  pose proof (convert_expression _ _ _ _ _ HMs Hdirect HE) as HMd.
  destruct (fresh_argument_quotation _ _ _ _ _ _ HQ HW) as (HT & HX & HXN & HXQ).
  destruct (HC _ _ _ _ HT HX HXN) as (b & HBe & HBq).
  destruct (Hact _ _ HW) as (x & y & b' & HF & HSnd & HBe' & Hqf & Hqs).
  pose proof (wf_fst _ _ _ _ _ HAs HBs HMd) as Hfst.
  pose proof (substitute_into_lift _ _ _ _ _ _ _ _ HS HA HB Hfst) as HsE.
  pose proof (instantiate_type _ _ _ _ HAs Hfst) as Hinst.
  pose proof (substitute_type _ _ _ _ _ Hinst HBs) as HsndB.
  eapply quote_term_type_conversion.
  - exact (substitute_type _ _ _ _ _ HS HP).
  - exact (wf_exp_eq_sym _ _ _ _ HE).
  - eapply quote_term_sigma; [exact HAs | exact HBs | exact HMd | | exact HBe | | exact HF | exact HSnd | exact HBe' | exact Hqf |].
    + exact (quotation_of_type _ _ _ _ HQ _ _ HW).
    + eapply observe_type; [exact (quotation_well_formed _ _ _ _ HBq) | exact (quotation_of_type _ _ _ _ HBq)].
    + eapply quote_term_type_conversion; [exact HsndB | exact (wf_exp_eq_sym _ _ _ _ HsE) | exact Hqs].
Qed.

Lemma finish_glued_pair : forall U Θ i A B a ρ C R T S M m,
    universe_invariants U -> universe_coherence U ->
    glued_type U Θ i A a R -> wf_exp (A :: Θ) (a_typ i) B ->
    at_type i (d_sigma a ρ C) (d_sigma a ρ C) S ->
    family_closes Θ ρ C R -> family_glues U Θ i B ρ C R T ->
    wf_exp Θ (a_sigma A B) M -> semantic_member (d_sigma a ρ C) m ->
    projectable R T Θ A B ρ C Θ a_id M m ->
    glued_term U Θ (a_sigma A B) M (d_sigma a ρ C) m.
Proof.
  intros U Θ i A B a ρ C R T S M m HU HC GA HB Hsem HF HT HM Hm Hproj.
  destruct (quoted_candidate_reflects _ _ _ _ _ _ HU GA) as (HQA & HRA).
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HA.
  pose proof (glued_type_sigma _ _ _ _ _ _ _ _ _ _ _ Hsem GA HB HF HT) as GP.
  eapply glued_at_candidate_identity; [exact GP |].
  pose proof (wf_sigma _ _ _ _ HA HB) as HP.
  destruct (preserve_at_id _ _ _ _ _ HP HM (reflexive_expression _ _ _ HM)) as (HMi & _).
  split; [exact HMi |]. split; [exact Hm |]. split; [|exact Hproj].
  pose proof (expression_context _ _ _ HM) as HG.
  pose proof (wf_sub_id _ HG) as HI.
  eapply convert_term_under_weakening.
  - exact (substitute_type _ _ _ _ _ HI HP).
  - apply wf_exp_eq_sym; now apply type_substitution_identity.
  - eapply quote_pair_action_on_neutrals; [exact HQA | exact HB | |exact HM |].
    + intros Ξ τ X n HW HX HN.
      pose proof (HRA _ _ _ _ HW HX HN) as HK.
      destruct (HF _ _ _ _ HW HK) as (b & Hb).
      exists b; split; [exact Hb |].
      exact (proj1 (quoted_candidate_reflects _ _ _ _ _ _ HU (HT _ _ _ _ HW HK _ Hb))).
    + intros Ξ τ HW.
      pose proof (weakening_identity _ HG) as Hid.
      pose proof (weakening_compose _ _ _ _ _ HW Hid) as Hcomp.
      destruct (Hproj _ _ HW) as (x & y & b & Hxe & Hye & Hbe & HX & HY).
      pose proof (HT _ _ _ _ Hcomp HX _ Hbe) as GB.
      pose proof (weakening_is_typed _ _ _ HW) as HS.
      pose proof (weakening_is_typed _ _ _ Hcomp) as HS'.
      pose proof (wf_sub_eq_id_compose_right _ _ _ HS) as HSE.
      destruct (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ Hcomp HX) as (HX' & _).
      pose proof (type_extension_congruence _ _ _ _ _ _ _ _ _ _ HS' HA HB HSE HX' (reflexive_expression _ _ _ HX')) as HBE.
      pose proof (reindex_candidate _ _ _ _ _ _ _ _ _ _ _ HU HC GA Hcomp HW HX) as HX''.
      destruct (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ HW HX'') as (HXt & _ & HXq).
      exists x, y, b; split; [exact Hxe |]. split; [exact Hye |]. split; [exact Hbe |].
      split; [exact (observe_term _ _ _ _ _ HXt HXq) |].
      eapply quote_term_type_conversion.
      * exact (substitute_type _ _ _ _ _ (wf_sub_extend _ _ _ _ _ _ HS HA HXt) HB).
      * exact HBE.
      * exact (glued_term_quote _ _ _ _ _ _ (glued_at_candidate_identity _ _ _ _ _ _ _ _ GB HY)).
Qed.

Lemma project_glued_value : forall U Θ i A B a ρ C R T M m S,
    universe_invariants U -> universe_coherence U ->
    glued_type U Θ i A a R -> wf_exp (A :: Θ) (a_typ i) B ->
    at_type i (d_sigma a ρ C) (d_sigma a ρ C) S ->
    family_closes Θ ρ C R -> family_glues U Θ i B ρ C R T ->
    glued_term U Θ (a_sigma A B) M (d_sigma a ρ C) m ->
    exists x y b, eval_fst m x /\ eval_snd m y /\ eval_exp C (extend_env ρ x) b /\
      glued_term U Θ A (a_fst M) a x /\
      glued_term U Θ (a_sub B (a_extend a_id (a_fst M))) (a_snd M) b y.
Proof.
  intros U Θ i A B a ρ C R T M m S HU HC GA HB Hsem HF HT GM.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HA.
  pose proof (glued_type_sigma _ _ _ _ _ _ _ _ _ _ _ Hsem GA HB HF HT) as GS.
  pose proof (candidate_at_identity _ _ _ _ _ _ _ _ HU HC GS GM) as (_ & _ & _ & Hproj).
  pose proof (expression_context _ _ _ HA) as HΘ.
  pose proof (weakening_identity _ HΘ) as Hid.
  pose proof (weakening_compose _ _ _ _ _ Hid Hid) as HII.
  destruct (Hproj _ _ Hid) as (x & y & b & Hxf & Hys & Hb & HX & HY).
  pose proof (glued_term_typing _ _ _ _ _ _ GM) as HM.
  pose proof (wf_exp_eq_sub_id _ _ _ HM) as HMe.
  pose proof (wf_fst _ _ _ _ _ HA HB HM) as HFst.
  pose proof (wf_snd _ _ _ _ _ HA HB HM) as HSnd.
  pose proof (wf_exp_eq_fst_cong _ _ _ _ _ _ HA HB HMe) as HFe.
  pose proof (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ HII HX) as (HXt & _).
  pose proof (reindex_candidate _ _ _ _ _ _ _ _ _ _ _ HU HC GA HII Hid HX) as HXi.
  pose proof (glued_at_candidate_identity _ _ _ _ _ _ _ _ GA HXi) as GX.
  pose proof (HT _ _ _ _ HII HX _ Hb) as GY.
  pose proof (weakening_is_typed _ _ _ HII) as HS.
  pose proof (wf_sub_id _ HΘ) as HI.
  pose proof (wf_sub_eq_id_compose_right _ _ _ HI) as HSe.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  assert (HAe : wf_exp_eq Θ (a_typ i) A (a_sub A (a_compose a_id a_id))).
  {
    apply wf_exp_eq_sym; eapply wf_exp_eq_trans; [|exact (type_substitution_identity _ _ _ HA)].
    eapply substitute_type_equality; [exact HS | exact HSe | now apply reflexive_expression].
  }
  pose proof (convert_equality _ _ _ _ _ _ HFe HAs HAe) as HFet.
  pose proof (type_extension_congruence _ _ _ _ _ _ _ _ _ _ HS HA HB HSe HXt HFet) as HBE.
  pose proof (substitute_type _ _ _ _ _ (instantiate_type _ _ _ _ HA HFst) HB) as HBT.
  pose proof (wf_exp_eq_snd_cong _ _ _ _ _ _ HA HB (wf_exp_eq_sym _ _ _ _ HMe)) as HSe'.
  exists x, y, b; split; [exact Hxf |]. split; [exact Hys |]. split; [exact Hb |].
  split.
  - exact (glued_term_expression_change _ _ _ _ _ _ _ HU HC GX HFst HFe).
  - eapply glued_term_expression_change; [exact HU | exact HC | | exact HSnd | exact (wf_exp_eq_sym _ _ _ _ HSe')].
    exact (glued_term_type_change _ _ _ _ _ _ _ _
      (glued_at_candidate_identity _ _ _ _ _ _ _ _ GY HY) HBT HBE).
Qed.

Lemma gluing_projections : forall k Γ i A B M,
    i < k ->
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    wf_exp Γ (a_sigma A B) M ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (a_typ i) B ->
    typing_respects_gluing (gluing_universes k) Γ (a_sigma A B) M ->
    typing_respects_gluing (gluing_universes k) Γ A (a_fst M) /\
    typing_respects_gluing (gluing_universes k) Γ (a_sub B (a_extend a_id (a_fst M))) (a_snd M).
Proof.
  intros k Γ i A B M Hk HA HB HM HAg HBg HMg.
  assert (Hproj : forall Θ σ ρ, glued_environment (gluing_universes k) Θ Γ σ ρ ->
    exists a x y b m,
      eval_exp A ρ a /\ eval_exp M ρ m /\ eval_fst m x /\ eval_snd m y /\ eval_exp B (extend_env ρ x) b /\
      glued_term (gluing_universes k) Θ (a_sub A σ) (a_sub (a_fst M) σ) a x /\
      glued_term (gluing_universes k) Θ (a_sub (a_sub B (a_extend a_id (a_fst M))) σ) (a_sub (a_snd M) σ) b y).
  {
    intros Θ σ ρ HE.
    pose proof (gluing_universes_quote k) as HU.
    pose proof (gluing_universes_coherent k) as HC.
    pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
    destruct (extract_glued_code _ _ _ _ _ _ _ Hk HE HAg) as (a & R & Hae & GA).
    destruct (construct_glued_family _ _ _ _ _ _ _ _ _ _ Hk HE HA HB Hae GA HBg) as (T & HF & HT).
    destruct (HMg _ _ _ HE) as (c & m & Hc & Hm & GM).
    assert (Hσe : eval_exp (a_sigma A B) ρ (d_sigma a ρ B)) by now apply eval_exp_sigma.
    pose proof (exp_unique _ _ _ Hc _ Hσe) as E; subst c.
    pose proof (wf_sigma _ _ _ _ HA HB) as HσT.
    destruct (semantically_typed_code _ _ _ _ _ HσT (glued_environment_semantic _ _ _ _ _ HE) Hσe) as (S & Hsem).
    pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
    pose proof (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HS HA) HB) as HBs.
    pose proof (wf_sigma _ _ _ _ HAs HBs) as HNative.
    pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as HσE.
    pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GM HNative HσE) as GM'.
    destruct (project_glued_value _ _ _ _ _ _ _ _ _ _ _ _ _
      HU HC GA HBs Hsem HF HT GM') as (x & y & b & Hxe & Hye & Hb & GX & GY).
    pose proof (wf_fst _ _ _ _ _ HA HB HM) as Hfst.
    pose proof (wf_snd _ _ _ _ _ HA HB HM) as Hsnd.
    pose proof (wf_exp_sub _ _ _ _ _ HS Hfst) as Hfsts.
    pose proof (wf_exp_sub _ _ _ _ _ HS Hsnd) as Hsnds.
    pose proof (wf_exp_eq_fst_sub _ _ _ _ _ _ _ HS HA HB HM) as HFe.
    pose proof (wf_exp_eq_snd_sub _ _ _ _ _ _ _ HS HA HB HM) as HYe.
    pose proof (glued_term_typing _ _ _ _ _ _ GX) as Hfst'.
    pose proof (wf_sub_extend _ _ _ _ _ _ HS HA Hfsts) as Hinst.
    pose proof (substitute_type _ _ _ _ _ Hinst HB) as HBT.
    pose proof (substitute_type _ _ _ _ _ (wf_sub_extend _ _ _ _ _ _ HS HA Hfst') HB) as HBTF.
    pose proof (type_extension_congruence _ _ _ _ _ _ _ _ _ _ HS HA HB (reflexive_substitution _ _ _ HS) Hfsts HFe) as HFBE.
    pose proof (substitute_into_lift _ _ _ _ _ _ _ _ HS HA HB Hfst') as HBE.
    pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GY HBTF HBE) as GY'.
    pose proof (substitute_instantiated_type _ _ _ _ _ _ _ _ HS HA HB Hfst) as HrawE.
    pose proof (substitute_type _ _ _ _ _ HS (substitute_type _ _ _ _ _
      (instantiate_type _ _ _ _ HA Hfst) HB)) as Hraw.
    assert (HEq : wf_exp_eq Θ (a_typ i) (a_sub (a_sub B (a_extend a_id (a_fst M))) σ)
        (a_sub B (a_extend σ (a_fst (a_sub M σ))))).
    { exact (wf_exp_eq_trans _ _ _ _ _ HrawE HFBE). }
    exists a, x, y, b, m; split; [exact Hae |]. split; [exact Hm |]. split; [exact Hxe |].
    split; [exact Hye |]. split; [exact Hb |]. split.
    - exact (glued_term_expression_change _ _ _ _ _ _ _ HU HC GX Hfsts (wf_exp_eq_sym _ _ _ _ HFe)).
    - eapply glued_term_type_change; [|exact Hraw|exact (wf_exp_eq_sym _ _ _ _ HEq)].
      eapply glued_term_expression_change;
        [exact HU | exact HC | exact GY' | exact (convert_expression _ _ _ _ _ Hsnds HBTF HEq)
        | exact (wf_exp_eq_sym _ _ _ _ HYe)].
  }
  split; intros Θ σ ρ HE;
    destruct (Hproj _ _ _ HE) as (a & x & y & b & m & Ha & Hm & Hx & Hy & Hb & GX & GY).
  - exists a,x; split; [exact Ha | split; [eapply eval_exp_fst; eassumption | exact GX]].
  - exists b,y; split; [|split; [eapply eval_exp_snd; eassumption | exact GY]].
    eapply eval_exp_sub; [eapply eval_sub_extend; [apply eval_sub_id | eapply eval_exp_fst; eassumption] | exact Hb].
Qed.

Lemma pair_beta_under_substitution : forall Θ Ξ i A B M N τ,
    wf_sub Ξ Θ τ -> wf_exp Θ (a_typ i) A ->
    wf_exp (A :: Θ) (a_typ i) B -> wf_exp Θ A M ->
    wf_exp Θ (a_sub B (a_extend a_id M)) N ->
    let P := a_sub (a_pair M A N B) τ in
    wf_exp_eq Ξ (a_sub A τ) (a_fst P) (a_sub M τ) /\
    wf_exp_eq Ξ (a_sub B (a_extend τ (a_sub M τ))) (a_snd P) (a_sub N τ).
Proof.
  intros Θ Ξ i A B M N τ HT HA HB HM HN; cbn zeta.
  pose proof (substitute_type _ _ _ _ _ HT HA) as HAs.
  pose proof (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HT HA) HB) as HBs.
  pose proof (wf_exp_sub _ _ _ _ _ HT HM) as HMs.
  pose proof (wf_sub_extend _ _ _ _ _ _ HT HA HMs) as HI.
  pose proof (substitute_type _ _ _ _ _ HI HB) as HBT.
  pose proof (substitute_into_lift _ _ _ _ _ _ _ _ HT HA HB HMs) as Hlift.
  pose proof (substitute_instantiated_type _ _ _ _ _ _ _ _ HT HA HB HM) as Hinst.
  pose proof (substitute_type _ _ _ _ _ (instantiate_type _ _ _ _ HAs HMs) HBs) as HBT'.
  pose proof (wf_exp_sub _ _ _ _ _ HT HN) as HNs.
  pose proof (convert_expression _ _ _ _ _ HNs HBT Hinst) as HNs'.
  pose proof (convert_expression _ _ _ _ _ HNs' HBT' (wf_exp_eq_sym _ _ _ _ Hlift)) as HNs''.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HT HA HB) as HsigE.
  pose proof (wf_exp_eq_pair_sub _ _ _ _ _ _ _ _ HT HA HB HM HN) as HPE.
  pose proof (convert_equality _ _ _ _ _ _ HPE (wf_sigma _ _ _ _ HAs HBs) HsigE) as HEP.
  pose proof (wf_exp_eq_fst_cong _ _ _ _ _ _ HAs HBs HEP) as HFE.
  pose proof (wf_exp_eq_fst_beta _ _ _ _ _ _ HAs HBs HMs HNs'') as HBf.
  pose proof (wf_exp_eq_trans _ _ _ _ _ HFE HBf) as Hfst.
  split; [exact Hfst |].
  eapply wf_exp_eq_trans;
    [|exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_snd_beta _ _ _ _ _ _ HAs HBs HMs HNs'') HBT Hlift)].
  pose proof (wf_exp_eq_snd_cong _ _ _ _ _ _ HAs HBs HEP) as HSE.
  pose proof (wf_pair _ _ _ _ _ _ HA HB HM HN) as HP.
  pose proof (convert_expression _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HT HP) (wf_sigma _ _ _ _ HAs HBs) HsigE) as HPs.
  pose proof (wf_fst _ _ _ _ _ HAs HBs HPs) as HFP.
  eapply convert_equality; [exact HSE | exact HBT |].
  eapply wf_exp_eq_trans; [exact (substitute_into_lift _ _ _ _ _ _ _ _ HT HA HB HFP) |].
  exact (type_extension_congruence _ _ _ _ _ _ _ _ _ _ HT HA HB (reflexive_substitution _ _ _ HT) HFP Hfst).
Qed.

Lemma gluing_pair : forall k Γ i A B M N,
    i < k ->
    wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    wf_exp Γ A M -> wf_exp Γ (a_sub B (a_extend a_id M)) N ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (a_typ i) B ->
    typing_respects_gluing (gluing_universes k) Γ A M ->
    typing_respects_gluing (gluing_universes k) Γ (a_sub B (a_extend a_id M)) N ->
    typing_respects_gluing (gluing_universes k) Γ (a_sigma A B) (a_pair M A N B).
Proof.
  intros k Γ i A B M N Hk HA HB HM HN HAg HBg HMg HNg Θ σ ρ HE.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (gluing_universes_weaken k) as HW.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  destruct (extract_glued_code _ _ _ _ _ _ _ Hk HE HAg) as (a & R & Hae & GA).
  destruct (construct_glued_family _ _ _ _ _ _ _ _ _ _ Hk HE HA HB Hae GA HBg) as (T & HF & HT).
  destruct (HMg _ _ _ HE) as (c & x & Hc & Hx & GX).
  destruct (HNg _ _ _ HE) as (b & y & Hb & Hy & GY).
  pose proof (exp_unique _ _ _ Hc _ Hae) as Hca; subst c.
  assert (Hbe : eval_exp B (extend_env ρ x) b).
  { inversion Hb; subst;
      try match goal with
      | Hsub : eval_sub (a_extend a_id M) ρ ?θ,
        Hbody : eval_exp B ?θ b |- _ =>
        assert (Hsx : eval_sub (a_extend a_id M) ρ (extend_env ρ x))
          by (apply eval_sub_extend; [apply eval_sub_id | exact Hx]);
        pose proof (sub_unique _ _ _ Hsub _ Hsx) as E; subst; exact Hbody
      end. }
  pose proof (wf_sigma _ _ _ _ HA HB) as HST.
  pose proof (wf_pair _ _ _ _ _ _ HA HB HM HN) as HOrig.
  assert (HSv : eval_exp (a_sigma A B) ρ (d_sigma a ρ B)) by now apply eval_exp_sigma.
  assert (HPv : eval_exp (a_pair M A N B) ρ (d_pair x y)) by now apply eval_exp_pair.
  destruct (semantically_typed_code _ _ _ _ _ HST (glued_environment_semantic _ _ _ _ _ HE) HSv) as (S & Hsem).
  pose proof (semantically_typed_value _ _ _ _ _ _ HOrig (glued_environment_semantic _ _ _ _ _ HE) HSv HPv) as Hmem.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HS HA) HB) as HBs.
  pose proof (wf_exp_sub _ _ _ _ _ HS HM) as HMw.
  pose proof (wf_exp_sub _ _ _ _ _ HS HN) as HNw.
  pose proof (substitute_type _ _ _ _ _ (wf_sub_extend _ _ _ _ _ _ HS HA HMw) HB) as HBd.
  pose proof (substitute_type _ _ _ _ _ (instantiate_type _ _ _ _ HAs HMw) HBs) as HBi.
  pose proof (substitute_instantiated_type _ _ _ _ _ _ _ _ HS HA HB HM) as HBE.
  pose proof (substitute_into_lift _ _ _ _ _ _ _ _ HS HA HB HMw) as HLI.
  pose proof (wf_exp_eq_trans _ _ _ _ _ HBE (wf_exp_eq_sym _ _ _ _ HLI)) as HBE'.
  pose proof (convert_expression _ _ _ _ _ HNw HBi HBE') as HNw'.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GY HBi HBE') as GY'.
  pose proof (wf_pair _ _ _ _ _ _ HAs HBs HMw HNw') as HP.
  assert (Hact : projectable R T Θ (a_sub A σ) (a_sub B (Syntax.q σ)) ρ B Θ a_id
      (a_pair (a_sub M σ) (a_sub A σ) (a_sub N σ) (a_sub B (Syntax.q σ))) (d_pair x y)).
  {
    intros Ξ τ Hτ.
    pose proof (weakening_is_typed _ _ _ Hτ) as Hτt.
    pose proof (weakening_identity _ (expression_context _ _ _ HAs)) as Hid.
    pose proof (weakening_compose _ _ _ _ _ Hτ Hid) as Hcomp.
    pose proof (glued_term_weaken _ _ _ _ _ _ _ _ HU HC HW Hτ GX) as GXw.
    pose proof (glued_term_weaken _ _ _ _ _ _ _ _ HU HC HW Hτ GY') as GYw.
    destruct (pair_beta_under_substitution _ _ _ _ _ _ _ _ Hτt HAs HBs HMw HNw') as (HFst & HSnd).
    destruct (project_under_weakening_typing _ _ _ _ _ _ _ _ _ HAs HBs Hid Hτ
      (proj1 (preserve_at_id _ _ _ _ _ (wf_sigma _ _ _ _ HAs HBs) HP (reflexive_expression _ _ _ HP))))
      as (HFt0 & HSt0).
    pose proof (weakening_is_typed _ _ _ Hcomp) as HCt.
    pose proof (wf_sub_eq_id_compose_right _ _ _ Hτt) as HcE.
    assert (HAE : wf_exp_eq Ξ (a_typ i) (a_sub (a_sub A σ) (a_compose a_id τ)) (a_sub (a_sub A σ) τ)).
    { eapply substitute_type_equality; [exact HCt | exact HcE | now apply reflexive_expression]. }
    pose proof (substitute_type _ _ _ _ _ Hτt HAs) as HAt.
    pose proof (convert_expression _ _ _ _ _ HFt0 HAt HAE) as HFt.
    pose proof (glued_term_expression_change _ _ _ _ _ _ _ HU HC GXw HFt (wf_exp_eq_sym _ _ _ _ HFst)) as GFst.
    pose proof (candidate_from_world _ _ _ _ _ _ _ _ _ _ HU HC GA Hτ GFst) as HRτ.
    pose proof (reindex_candidate _ _ _ _ _ _ _ _ _ _ _ HU HC GA Hτ Hcomp HRτ) as HR.
    pose proof (wf_exp_sub _ _ _ _ _ Hτt HMw) as Hfstw.
    pose proof (substitute_type _ _ _ _ _ (wf_sub_extend _ _ _ _ _ _ Hτt HAs Hfstw) HBs) as HYt.
    pose proof (substitute_instantiated_type _ _ _ _ _ _ _ _ Hτt HAs HBs HMw) as HYE.
    pose proof (type_extension_congruence _ _ _ _ _ _ _ _ _ _ Hτt HAs HBs (reflexive_substitution _ _ _ Hτt)
      HFt HFst) as HFE.
    pose proof (substitute_type _ _ _ _ _ (wf_sub_extend _ _ _ _ _ _ Hτt HAs HFt) HBs) as HYt'.
    pose proof (type_extension_congruence _ _ _ _ _ _ _ _ _ _ HCt HAs HBs HcE HFt0
      (reflexive_expression _ _ _ HFt0)) as HcBE.
    pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GYw HYt HYE) as GYt.
    exists x, y, b; split; [apply eval_fst_pair |]. split; [apply eval_snd_pair |].
    split; [exact Hbe |]. split; [exact HR |].
    eapply glued_family_identity; [exact HU | exact HC | exact GA | exact HBs | exact HT | exact Hτ | exact HR | exact Hbe |].
    eapply glued_term_type_change; [|exact HYt'|exact (wf_exp_eq_sym _ _ _ _ HFE)].
    eapply glued_term_expression_change;
      [exact HU | exact HC | exact GYt | | exact (wf_exp_eq_sym _ _ _ _ HSnd)].
    eapply convert_expression; [exact HSt0 | exact HYt |].
    exact (wf_exp_eq_trans _ _ _ _ _ HcBE HFE).
  }
  pose proof (finish_glued_pair _ _ _ _ _ _ _ _ _ _ _ _ _ HU HC GA HBs Hsem HF HT HP Hmem Hact) as GP.
  pose proof (substitute_type _ _ _ _ _ HS HST) as HSTs.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB)) as HSE.
  exists (d_sigma a ρ B), (d_pair x y); split; [exact HSv |]. split; [exact HPv |].
  eapply glued_term_expression_change;
    [exact HU | exact HC | exact (glued_term_type_change _ _ _ _ _ _ _ _ GP HSTs HSE)
    | exact (wf_exp_sub _ _ _ _ _ HS HOrig) |].
  apply wf_exp_eq_sym; exact (wf_exp_eq_pair_sub _ _ _ _ _ _ _ _ HS HA HB HM HN).
Qed.

Definition subtype_respects_gluing U Γ A B :=
  forall Θ σ ρ M a m,
    glued_environment U Θ Γ σ ρ -> eval_exp A ρ a ->
    glued_term U Θ (a_sub A σ) M a m ->
    exists b, eval_exp B ρ b /\ glued_term U Θ (a_sub B σ) M b m.

Definition context_inclusion_respects_gluing U Γ Δ :=
  forall Θ σ ρ, glued_environment U Θ Γ σ ρ -> glued_environment U Θ Δ σ ρ.

Lemma gluing_subtype_conversion : forall U Γ A B i,
    universe_invariants U -> universe_coherence U ->
    wf_exp Γ (a_typ i) B -> wf_exp_eq Γ (a_typ i) A B ->
    subtype_respects_gluing U Γ A B.
Proof. intros; exact (gluing_convert_type_at_environment _ _ _ _ _ H H0 H1 H2). Qed.

Lemma gluing_subtype_trans : forall U Γ A B C,
    subtype_respects_gluing U Γ A B -> subtype_respects_gluing U Γ B C ->
    subtype_respects_gluing U Γ A C.
Proof.
  intros U Γ A B C H1 H2 Θ σ ρ M a m HE HA GM.
  destruct (H1 _ _ _ _ _ _ HE HA GM) as (b & HB & GMB).
  exact (H2 _ _ _ _ _ _ HE HB GMB).
Qed.

Lemma gluing_subtype_universe : forall k Γ i j,
    i <= j -> j < k ->
    subtype_respects_gluing (gluing_universes k) Γ (a_typ i) (a_typ j).
Proof.
  intros k Γ i j Hle Hk Θ σ ρ M a m HE Ha GM.
  inversion Ha; subst a.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (proj1 (substitution_contexts _ _ _ HS)) as HΘ.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  assert (Hi : i < k) by lia.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GM (wf_typ Θ i HΘ)
    (wf_exp_eq_typ_sub _ _ _ _ HS)) as GM'.
  destruct (glued_code_from_term _ _ _ _ _ Hi GM') as (R & GR).
  pose proof (glued_type_cumulative _ _ _ _ _ _ _ GR Hle) as GR'.
  exists (d_univ j); split; [apply eval_exp_typ |].
  eapply glued_term_type_change; [exact (type_gluing_as_term _ _ _ _ _ _ Hk GR') | |].
  - exact (substitute_type _ _ _ _ _ HS (wf_typ Γ j (proj2 (substitution_contexts _ _ _ HS)))).
  - apply wf_exp_eq_sym; exact (wf_exp_eq_typ_sub _ _ _ _ HS).
Qed.

Lemma gluing_exp_subtype : forall U Γ A B M,
    subtype_respects_gluing U Γ A B ->
    typing_respects_gluing U Γ A M ->
    typing_respects_gluing U Γ B M.
Proof.
  intros U Γ A B M Hsub HM Θ σ ρ HE.
  destruct (HM _ _ _ HE) as (a & m & Ha & Hm & GM).
  destruct (Hsub _ _ _ _ _ _ HE Ha GM) as (b & Hb & GM').
  exists b, m; tauto.
Qed.

Lemma gluing_sub_context_inclusion : forall U Γ Δ Ξ τ,
    substitution_respects_gluing U Γ Δ τ ->
    context_inclusion_respects_gluing U Δ Ξ ->
    substitution_respects_gluing U Γ Ξ τ.
Proof.
  intros U Γ Δ Ξ τ Hs Hsub Θ σ ρ HE.
  destruct (Hs _ _ _ HE) as (θ & Hθ & Hg).
  exists θ; split; [exact Hθ | now apply Hsub].
Qed.

Lemma gluing_context_inclusion_extend : forall U Γ Δ A B i,
    wf_ctx_sub Γ Δ -> wf_exp Γ (a_typ i) A -> wf_exp Δ (a_typ i) B ->
    wf_subtyp Γ A B ->
    context_inclusion_respects_gluing U Γ Δ ->
    subtype_respects_gluing U Γ A B ->
    context_inclusion_respects_gluing U (A :: Γ) (B :: Δ).
Proof.
  intros U Γ Δ A B i HD HA HB HAB Hctx Hsub Θ σ ρ HE.
  inversion HE as [|Γ' A' j σ' ρ' a HS HA' Henv Hae HM Hcan]; subst.
  pose proof (wf_ctx_sub_extend _ _ _ _ _ HD HA HB HAB) as Hext.
  pose proof (expression_context _ _ _ HB) as HΔ.
  pose proof (wf_sub_subtyp _ _ _ _ HS (wf_ctx_extend _ _ _ HΔ HB) Hext) as HS'.
  destruct (Hsub _ _ _ _ _ _ Henv Hae HM) as (b & Hbe & Hmb).
  eapply glued_environment_cons;
    [exact HS' | exact HB | exact (Hctx _ _ _ Henv) | exact Hbe | exact Hmb | exact Hcan].
Qed.

Lemma subtype_substitution : forall Γ A B,
    wf_subtyp Γ A B -> forall Θ σ, wf_sub Θ Γ σ ->
    wf_subtyp Θ (a_sub A σ) (a_sub B σ).
Proof.
  intros Γ A B H.
  induction H as [Γ A B i HB HAB|Γ A B C H1 IH1 H2 IH2|Γ i j HΓ Hij
    |Γ A B A' B' i HA HA' HE HB HB' Hsub IH
    |Γ A B A' B' i HA HA' HE HB HB' Hsub IH]; intros Θ σ HS.
  - eapply wf_subtyp_refl.
    + exact (substitute_type _ _ _ _ _ HS HB).
    + eapply substitute_type_equality; [exact HS | now apply reflexive_substitution | exact HAB].
  - eapply wf_subtyp_trans; [exact (IH1 _ _ HS) | exact (IH2 _ _ HS)].
  - pose proof (proj1 (substitution_contexts _ _ _ HS)) as HΘ.
    eapply wf_subtyp_trans.
    + exact (wf_subtyp_refl _ _ _ _ (wf_typ Θ i HΘ) (wf_exp_eq_typ_sub _ _ _ _ HS)).
    + eapply wf_subtyp_trans.
      * exact (wf_subtyp_univ _ _ _ HΘ Hij).
      * exact (wf_subtyp_refl _ _ _ _ (substitute_type _ _ _ _ _ HS (wf_typ _ j HΓ))
          (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_typ_sub _ _ _ _ HS))).
  - pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
    pose proof (substitute_type _ _ _ _ _ HS HA') as HA's.
    pose proof (lift_substitution _ _ _ _ _ HS HA) as HT.
    pose proof (lift_substitution _ _ _ _ _ HS HA') as HT'.
    pose proof (substitute_type _ _ _ _ _ HT HB) as HBs.
    pose proof (substitute_type _ _ _ _ _ HT' HB') as HB's.
    pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB) as HP.
    pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA' HB') as HP'.
    eapply wf_subtyp_trans.
    + exact (wf_subtyp_refl _ _ _ _ (wf_pi _ _ _ _ HAs HBs) HP).
    + eapply wf_subtyp_trans.
      * eapply wf_subtyp_pi; [exact HAs | exact HA's | | exact HBs | exact HB's | exact (IH _ _ HT')].
        eapply substitute_type_equality; [exact HS | now apply reflexive_substitution | exact HE].
      * exact (wf_subtyp_refl _ _ _ _ (substitute_type _ _ _ _ _ HS (wf_pi _ _ _ _ HA' HB'))
          (wf_exp_eq_sym _ _ _ _ HP')).
  - pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
    pose proof (substitute_type _ _ _ _ _ HS HA') as HA's.
    pose proof (lift_substitution _ _ _ _ _ HS HA) as HT.
    pose proof (lift_substitution _ _ _ _ _ HS HA') as HT'.
    pose proof (substitute_type _ _ _ _ _ HT HB) as HBs.
    pose proof (substitute_type _ _ _ _ _ HT' HB') as HB's.
    pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as HP.
    pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA' HB') as HP'.
    eapply wf_subtyp_trans.
    + exact (wf_subtyp_refl _ _ _ _ (wf_sigma _ _ _ _ HAs HBs) HP).
    + eapply wf_subtyp_trans.
      * eapply wf_subtyp_sigma; [exact HAs | exact HA's | | exact HBs | exact HB's | exact (IH _ _ HT')].
        eapply substitute_type_equality; [exact HS | now apply reflexive_substitution | exact HE].
      * exact (wf_subtyp_refl _ _ _ _ (substitute_type _ _ _ _ _ HS (wf_sigma _ _ _ _ HA' HB'))
          (wf_exp_eq_sym _ _ _ _ HP')).
Qed.

Lemma semantic_subtype_member : forall Γ A B ρ a b m,
    wf_subtyp Γ A B -> env_related Γ ρ ρ ->
    eval_exp A ρ a -> eval_exp B ρ b ->
    semantic_member a m -> semantic_member b m.
Proof.
  intros Γ A B ρ a b m Hsub Hρ HA HB (j & V & HV & Hm).
  destruct fundamental_evaluation as (_ & _ & _ & _ & _ & _ & Hsemantic).
  destruct (Hsemantic _ _ _ Hsub _ _ Hρ) as
    (S & T & (a' & a'' & Ha' & Ha'' & HSa) & (b' & b'' & Hb' & Hb'' & HSb) & Hrel).
  resolve_eval.
  destruct HSa as (i & HS).
  destruct HSb as (l & HT).
  exists l, T; split; [exact HT |].
  apply Hrel.
  exact (proj1 (at_type_coherent_l _ _ _ _ _ _ _ HV HS _ _) Hm).
Qed.

Lemma equivalent_candidate_at_world : forall U Γ Ξ i A B a b R T τ V M m,
    universe_invariants U -> universe_coherence U ->
    glued_type U Γ i A a R -> glued_type U Γ i B b T ->
    weakening Ξ Γ τ -> at_type i a b V ->
    R Ξ τ M m -> T Ξ τ M m.
Proof.
  intros U Γ Ξ i A B a b R T τ V M m HU HC GA GB Hτ HV HM.
  destruct (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ Hτ HM) as (HMt & (j & S & HS & Hm) & _).
  eapply move_candidate;
    [exact HU | exact HC | exact GA | exact GB | exact Hτ | exact Hτ | exact HV | | exact HM | | now apply reflexive_expression].
  - exact (proj2 (at_type_coherent_l _ _ _ _ _ _ _ HV HS _ _) Hm).
  - eapply type_gluing_move_term; [exact HU | exact GA | exact GB | exact Hτ | exact Hτ | exact HV | exact HMt].
Qed.

Lemma gluing_family_transport : forall k Γ Θ Ξ i σ τ ρ A A' B B' a' X x Y b y,
    glued_environment (gluing_universes k) Θ Γ σ ρ ->
    weakening Ξ Θ τ ->
    wf_exp Γ (a_typ i) A -> wf_exp Γ (a_typ i) A' ->
    wf_exp (A :: Γ) (a_typ i) B -> wf_exp (A' :: Γ) (a_typ i) B' ->
    eval_exp A' ρ a' ->
    wf_exp Ξ (a_sub (a_sub A σ) τ) X ->
    glued_term (gluing_universes k) Ξ (a_sub (a_sub A' σ) τ) X a' x ->
    subtype_respects_gluing (gluing_universes k) (A' :: Γ) B B' ->
    eval_exp B (extend_env ρ x) b ->
    glued_term (gluing_universes k) Ξ (a_sub (a_sub B (Syntax.q σ)) (a_extend τ X)) Y b y ->
    exists b', eval_exp B' (extend_env ρ x) b' /\
      glued_term (gluing_universes k) Ξ (a_sub (a_sub B' (Syntax.q σ)) (a_extend τ X)) Y b' y.
Proof.
  intros k Γ Θ Ξ i σ τ ρ A A' B B' a' X x Y b y HE Hτ HA HA' HB HB' Ha' HX GX Hsub Hb GY.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (gluing_universes_weaken k) as HW.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (weakening_is_typed _ _ _ Hτ) as HT.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HCt.
  pose proof (substitute_type _ _ _ _ _ HCt HA) as HAct.
  pose proof (substitute_type _ _ _ _ _ HCt HA') as HAct'.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_compose _ _ _ _ _ _ _ HT HS HA)) as HAe.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_compose _ _ _ _ _ _ _ HT HS HA')) as HAe'.
  pose proof (convert_expression _ _ _ _ _ HX HAct HAe) as HXc.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GX HAct' HAe') as GXc.
  pose proof (glued_term_typing _ _ _ _ _ _ GXc) as HXc'.
  pose proof (instantiate_glued_environment _ _ _ _ _ _ _ _ _ _ _ _ HU HC HW HE Hτ HA' Ha' GXc) as HE'.
  pose proof (type_after_lift_instantiation _ _ _ _ _ _ _ _ _ _ HT HS HA HXc HB) as HBE.
  pose proof (type_after_lift_instantiation _ _ _ _ _ _ _ _ _ _ HT HS HA' HXc' HB') as HBE'.
  pose proof (wf_sub_extend _ _ _ _ _ _ HCt HA HXc) as Hext.
  pose proof (substitute_type _ _ _ _ _ Hext HB) as HBt.
  destruct (Hsub _ _ _ _ _ _ HE' Hb (glued_term_type_change _ _ _ _ _ _ _ _ GY HBt HBE))
    as (b' & Hb' & GY').
  destruct (typed_lift_instantiation _ _ _ _ _ _ _ _ HT HS HA' HXc') as (Hlift & _).
  pose proof (substitute_type _ _ _ _ _ Hlift (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HS HA') HB')) as HBT.
  exists b'; split; [exact Hb' |].
  exact (glued_term_type_change _ _ _ _ _ _ _ _ GY' HBT (wf_exp_eq_sym _ _ _ _ HBE')).
Qed.

Lemma family_term_from_action : forall U Θ i A B a ρ C R T Ξ τ X x b Y y,
    universe_invariants U -> universe_coherence U ->
    glued_type U Θ i A a R -> wf_exp (A :: Θ) (a_typ i) B ->
    family_glues U Θ i B ρ C R T ->
    weakening Ξ Θ τ ->
    R Ξ (a_compose a_id τ) X x ->
    eval_exp C (extend_env ρ x) b ->
    T Ξ (a_compose a_id τ) X x Ξ a_id Y y ->
    glued_term U Ξ (a_sub B (a_extend τ X)) Y b y.
Proof.
  intros U Θ i A B a ρ C R T Ξ τ X x b Y y HU HC GA HB HT HW HX Hb HY.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HA.
  pose proof (weakening_identity _ (expression_context _ _ _ HA)) as HI.
  pose proof (weakening_compose _ _ _ _ _ HW HI) as Ht.
  pose proof (weakening_is_typed _ _ _ HW) as HS.
  pose proof (weakening_is_typed _ _ _ Ht) as HS'.
  pose proof (wf_sub_eq_id_compose_right _ _ _ HS) as HE.
  pose proof (HT _ _ _ _ Ht HX _ Hb) as GY.
  pose proof (reindex_candidate _ _ _ _ _ _ _ _ _ _ _ HU HC GA Ht HW HX) as HX'.
  destruct (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ Ht HX) as (HXc & _).
  destruct (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ HW HX') as (HXt & _).
  eapply glued_term_type_change.
  - exact (glued_at_candidate_identity _ _ _ _ _ _ _ _ GY HY).
  - exact (substitute_type _ _ _ _ _ (wf_sub_extend _ _ _ _ _ _ HS HA HXt) HB).
  - exact (type_extension_congruence _ _ _ _ _ _ _ _ _ _ HS' HA HB HE HXc (reflexive_expression _ _ _ HXc)).
Qed.

Lemma gluing_subtype_binder_data : forall k Γ Θ i A B A' B' σ ρ,
    i < k -> glued_environment (gluing_universes k) Θ Γ σ ρ ->
    wf_exp Γ (a_typ i) A -> wf_exp Γ (a_typ i) A' ->
    wf_exp_eq Γ (a_typ i) A A' ->
    wf_exp (A :: Γ) (a_typ i) B -> wf_exp (A' :: Γ) (a_typ i) B' ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A' ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (a_typ i) B ->
    typing_respects_gluing (gluing_universes k) (A' :: Γ) (a_typ i) B' ->
    exists a a' R R' T T' V,
      eval_exp A ρ a /\ eval_exp A' ρ a' /\ at_type i a a' V /\
      glued_type (gluing_universes k) Θ i (a_sub A σ) a R /\
      glued_type (gluing_universes k) Θ i (a_sub A' σ) a' R' /\
      family_closes Θ ρ B R /\ family_closes Θ ρ B' R' /\
      family_glues (gluing_universes k) Θ i (a_sub B (Syntax.q σ)) ρ B R T /\
      family_glues (gluing_universes k) Θ i (a_sub B' (Syntax.q σ)) ρ B' R' T'.
Proof.
  intros k Γ Θ i A B A' B' σ ρ Hk HEnv HA HA' HE HB HB' HAg HAg' HBg HBg'.
  destruct (extract_glued_code _ _ _ _ _ _ _ Hk HEnv HAg) as (a & R & Hav & GA).
  destruct (extract_glued_code _ _ _ _ _ _ _ Hk HEnv HAg') as (a' & R' & Hav' & GA').
  destruct (construct_glued_family _ _ _ _ _ _ _ _ _ _ Hk HEnv HA HB Hav GA HBg) as (T & HF & HT).
  destruct (construct_glued_family _ _ _ _ _ _ _ _ _ _ Hk HEnv HA' HB' Hav' GA' HBg') as (T' & HF' & HT').
  destruct fundamental_evaluation as (_ & _ & _ & Heq & _).
  destruct (from_universe _ _ _ _ _ (proj1 (Heq _ _ _ _ HE) _ _
      (glued_environment_semantic _ _ _ _ _ HEnv))) as (ax & ay & Hax & Hay & V & HV).
  resolve_eval.
  exists a, a', R, R', T, T', V; repeat split; assumption.
Qed.

Lemma gluing_subtype_pi : forall k Γ i A B A' B',
    i < k -> wf_exp Γ (a_typ i) A -> wf_exp Γ (a_typ i) A' ->
    wf_exp_eq Γ (a_typ i) A A' ->
    wf_exp (A :: Γ) (a_typ i) B -> wf_exp (A' :: Γ) (a_typ i) B' ->
    wf_subtyp (A' :: Γ) B B' ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A' ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (a_typ i) B ->
    typing_respects_gluing (gluing_universes k) (A' :: Γ) (a_typ i) B' ->
    subtype_respects_gluing (gluing_universes k) (A' :: Γ) B B' ->
    subtype_respects_gluing (gluing_universes k) Γ (a_pi A B) (a_pi A' B').
Proof.
  intros k Γ i A B A' B' Hk HA HA' HE HB HB' Hsub HAg HAg' HBg HBg' Hsubg Θ σ ρ M p m HEnv Hp Gm.
  destruct (gluing_subtype_binder_data _ _ _ _ _ _ _ _ _ _ Hk HEnv HA HA' HE HB HB' HAg HAg' HBg HBg')
    as (a & a' & R & R' & T & T' & V & Hav & Hav' & HV & GA & GA' & HF & HF' & HT & HT').
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (glued_environment_typing _ _ _ _ _ HEnv) as HS.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (substitute_type _ _ _ _ _ HS HA') as HA's.
  pose proof (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HS HA) HB) as HBs.
  pose proof (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HS HA') HB') as HB's.
  pose proof (wf_pi _ _ _ _ HA HB) as HP.
  pose proof (wf_pi _ _ _ _ HA' HB') as HP'.
  pose proof (wf_pi _ _ _ _ HAs HBs) as HPS.
  pose proof (wf_pi _ _ _ _ HA's HB's) as HPS'.
  pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA HB) as HPE.
  pose proof (wf_exp_eq_pi_sub _ _ _ _ _ _ HS HA' HB') as HPE'.
  assert (HPI : eval_exp (a_pi A B) ρ (d_pi a ρ B)) by now apply eval_exp_pi.
  assert (HPI' : eval_exp (a_pi A' B') ρ (d_pi a' ρ B')) by now apply eval_exp_pi.
  pose proof (exp_unique _ _ _ Hp _ HPI) as Hcp; subst p.
  pose proof (glued_environment_semantic _ _ _ _ _ HEnv) as Hρ.
  destruct (semantically_typed_code _ _ _ _ _ HP Hρ HPI) as (S & Hsem).
  destruct (semantically_typed_code _ _ _ _ _ HP' Hρ HPI') as (S' & Hsem').
  pose proof (wf_subtyp_pi _ _ _ _ _ _ HA HA' HE HB HB' Hsub) as HsubP.
  pose proof (glued_term_typing _ _ _ _ _ _ Gm) as HM.
  pose proof (substitute_type _ _ _ _ _ HS HP') as HP's.
  pose proof (wf_exp_subtyp _ _ _ _ _ HM HP's (subtype_substitution _ _ _ HsubP _ _ HS)) as HM'.
  pose proof (convert_expression _ _ _ _ _ HM' HPS' HPE') as HM''.
  pose proof (glued_type_pi _ _ _ _ _ _ _ _ _ _ _ Hsem GA HBs HF HT) as GPI.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ Gm HPS HPE) as GM.
  pose proof (candidate_at_identity _ _ _ _ _ _ _ _ HU HC GPI GM) as (_ & Hmem & _ & Hcall).
  pose proof (semantic_subtype_member _ _ _ _ _ _ _ HsubP Hρ HPI HPI' Hmem) as Hmem'.
  assert (Hcall' : callable R' T' Θ (a_sub A' σ) (a_sub B' (Syntax.q σ)) ρ B' Θ a_id M m).
  {
    intros Ξ τ X x Hτ HX'.
    pose proof (weakening_identity _ (expression_context _ _ _ HAs)) as Hid.
    pose proof (weakening_compose _ _ _ _ _ Hτ Hid) as Ht.
    pose proof (equivalent_candidate_at_world _ _ _ _ _ _ _ _ _ _ _ _ _ _ HU HC GA' GA Ht
      (at_type_sym _ _ _ _ HV) HX') as HX.
    destruct (Hcall _ _ _ _ Hτ HX) as (b & y & Hb & Hy & HRY).
    pose proof (family_term_from_action _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HU HC GA HBs HT Hτ HX Hb HRY) as GY.
    pose proof (reindex_candidate _ _ _ _ _ _ _ _ _ _ _ HU HC GA Ht Hτ HX) as HXτ.
    pose proof (reindex_candidate _ _ _ _ _ _ _ _ _ _ _ HU HC GA' Ht Hτ HX') as HXτ'.
    destruct (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ Hτ HXτ) as (HXt & _).
    pose proof (candidate_to_world _ _ _ _ _ _ _ _ _ _ HU HC GA' Hτ HXτ') as GX.
    destruct (gluing_family_transport _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEnv Hτ HA HA' HB HB' Hav'
      HXt GX Hsubg Hb GY) as (b' & Hb' & GY').
    exists b', y; split; [exact Hb' |]. split; [exact Hy |].
    eapply glued_family_identity; [exact HU | exact HC | exact GA' | exact HB's | exact HT' | exact Hτ | exact HX' | exact Hb' | exact GY'].
  }
  pose proof (finish_glued_function _ _ _ _ _ _ _ _ _ _ _ _ _ HU HC GA' HB's Hsem' HF' HT' HM'' Hmem' Hcall') as GFn.
  exists (d_pi a' ρ B'); split; [exact HPI' |].
  exact (glued_term_type_change _ _ _ _ _ _ _ _ GFn HP's (wf_exp_eq_sym _ _ _ _ HPE')).
Qed.

Lemma gluing_subtype_sigma : forall k Γ i A B A' B',
    i < k -> wf_exp Γ (a_typ i) A -> wf_exp Γ (a_typ i) A' ->
    wf_exp_eq Γ (a_typ i) A A' ->
    wf_exp (A :: Γ) (a_typ i) B -> wf_exp (A' :: Γ) (a_typ i) B' ->
    wf_subtyp (A' :: Γ) B B' ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A' ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (a_typ i) B ->
    typing_respects_gluing (gluing_universes k) (A' :: Γ) (a_typ i) B' ->
    subtype_respects_gluing (gluing_universes k) (A' :: Γ) B B' ->
    subtype_respects_gluing (gluing_universes k) Γ (a_sigma A B) (a_sigma A' B').
Proof.
  intros k Γ i A B A' B' Hk HA HA' HE HB HB' Hsub HAg HAg' HBg HBg' Hsubg Θ σ ρ M p m HEnv Hp Gm.
  destruct (gluing_subtype_binder_data _ _ _ _ _ _ _ _ _ _ Hk HEnv HA HA' HE HB HB' HAg HAg' HBg HBg')
    as (a & a' & R & R' & T & T' & V & Hav & Hav' & HV & GA & GA' & HF & HF' & HT & HT').
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (glued_environment_typing _ _ _ _ _ HEnv) as HS.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (substitute_type _ _ _ _ _ HS HA') as HA's.
  pose proof (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HS HA) HB) as HBs.
  pose proof (substitute_type _ _ _ _ _ (lift_substitution _ _ _ _ _ HS HA') HB') as HB's.
  pose proof (wf_sigma _ _ _ _ HA HB) as HP.
  pose proof (wf_sigma _ _ _ _ HA' HB') as HP'.
  pose proof (wf_sigma _ _ _ _ HAs HBs) as HPS.
  pose proof (wf_sigma _ _ _ _ HA's HB's) as HPS'.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA HB) as HPE.
  pose proof (wf_exp_eq_sigma_sub _ _ _ _ _ _ HS HA' HB') as HPE'.
  assert (HPI : eval_exp (a_sigma A B) ρ (d_sigma a ρ B)) by now apply eval_exp_sigma.
  assert (HPI' : eval_exp (a_sigma A' B') ρ (d_sigma a' ρ B')) by now apply eval_exp_sigma.
  pose proof (exp_unique _ _ _ Hp _ HPI) as Hcp; subst p.
  pose proof (glued_environment_semantic _ _ _ _ _ HEnv) as Hρ.
  destruct (semantically_typed_code _ _ _ _ _ HP Hρ HPI) as (S & Hsem).
  destruct (semantically_typed_code _ _ _ _ _ HP' Hρ HPI') as (S' & Hsem').
  pose proof (wf_subtyp_sigma _ _ _ _ _ _ HA HA' HE HB HB' Hsub) as HsubP.
  pose proof (glued_term_typing _ _ _ _ _ _ Gm) as HM.
  pose proof (substitute_type _ _ _ _ _ HS HP') as HP's.
  pose proof (wf_exp_subtyp _ _ _ _ _ HM HP's (subtype_substitution _ _ _ HsubP _ _ HS)) as HM'.
  pose proof (convert_expression _ _ _ _ _ HM' HPS' HPE') as HM''.
  pose proof (glued_type_sigma _ _ _ _ _ _ _ _ _ _ _ Hsem GA HBs HF HT) as GPI.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ Gm HPS HPE) as GM.
  pose proof (candidate_at_identity _ _ _ _ _ _ _ _ HU HC GPI GM) as (_ & Hmem & _ & Hproj).
  pose proof (semantic_subtype_member _ _ _ _ _ _ _ HsubP Hρ HPI HPI' Hmem) as Hmem'.
  assert (Hproj' : projectable R' T' Θ (a_sub A' σ) (a_sub B' (Syntax.q σ)) ρ B' Θ a_id M m).
  {
    intros Ξ τ Hτ.
    pose proof (weakening_identity _ (expression_context _ _ _ HAs)) as Hid.
    pose proof (weakening_compose _ _ _ _ _ Hτ Hid) as Ht.
    destruct (Hproj _ _ Hτ) as (x & y & b & Hx & Hy & Hb & HX & HRY).
    pose proof (equivalent_candidate_at_world _ _ _ _ _ _ _ _ _ _ _ _ _ _ HU HC GA GA' Ht HV HX) as HX'.
    pose proof (family_term_from_action _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HU HC GA HBs HT Hτ HX Hb HRY) as GY.
    pose proof (reindex_candidate _ _ _ _ _ _ _ _ _ _ _ HU HC GA Ht Hτ HX) as HXτ.
    pose proof (reindex_candidate _ _ _ _ _ _ _ _ _ _ _ HU HC GA' Ht Hτ HX') as HXτ'.
    destruct (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ Hτ HXτ) as (HXt & _).
    pose proof (candidate_to_world _ _ _ _ _ _ _ _ _ _ HU HC GA' Hτ HXτ') as GX.
    destruct (gluing_family_transport _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEnv Hτ HA HA' HB HB' Hav'
      HXt GX Hsubg Hb GY) as (b' & Hb' & GY').
    exists x, y, b'; split; [exact Hx |]. split; [exact Hy |]. split; [exact Hb' |]. split; [exact HX' |].
    eapply glued_family_identity; [exact HU | exact HC | exact GA' | exact HB's | exact HT' | exact Hτ | exact HX' | exact Hb' | exact GY'].
  }
  pose proof (finish_glued_pair _ _ _ _ _ _ _ _ _ _ _ _ _ HU HC GA' HB's Hsem' HF' HT' HM'' Hmem' Hproj') as GPair.
  exists (d_sigma a' ρ B'); split; [exact HPI' |].
  exact (glued_term_type_change _ _ _ _ _ _ _ _ GPair HP's (wf_exp_eq_sym _ _ _ _ HPE')).
Qed.

Definition code_respects_gluing k Γ A :=
  exists i, i < k /\ wf_exp Γ (a_typ i) A /\ typing_respects_gluing (gluing_universes k) Γ (a_typ i) A.

Definition context_types_respect_gluing k Γ :=
  forall x A, ctx_lookup x A Γ -> code_respects_gluing k Γ A.

Definition gluing_context_valid k Γ :=
  initial_environment_respects_gluing (gluing_universes k) Γ /\ context_types_respect_gluing k Γ.

Definition gluing_typing_valid k Γ A M :=
  typing_respects_gluing (gluing_universes k) Γ A M /\ code_respects_gluing k Γ A.

Lemma gluing_context_empty : forall k, gluing_context_valid k nil.
Proof.
  intros k; split; [apply initial_environment_empty | intros x A H; inversion H].
Qed.

Lemma gluing_context_extend : forall k Γ A i,
    i < k -> wf_exp Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    gluing_context_valid k Γ -> gluing_context_valid k (A :: Γ).
Proof.
  intros k Γ A i Hk HA HAg (Hinit & Htypes).
  split; [eapply initial_environment_extend; eassumption |].
  intros x B HL.
  pose proof (wf_ctx_extend _ _ _ (expression_context _ _ _ HA) HA) as Hctx.
  pose proof (wf_sub_weaken _ _ Hctx) as Hwk.
  inversion HL; subst.
  - exists i; split; [exact Hk |]. split; [exact (substitute_type _ _ _ _ _ Hwk HA) |].
    eapply gluing_type_substitution; [apply gluing_universes_quote | apply gluing_universes_coherent |
      exact Hwk | exact HA | apply gluing_sub_weaken | exact HAg].
  - match goal with H : ctx_lookup _ ?C Γ |- _ => destruct (Htypes _ _ H) as (j & Hj & HC & HCg) end.
    exists j; split; [exact Hj |]. split; [exact (substitute_type _ _ _ _ _ Hwk HC) |].
    eapply gluing_type_substitution; [apply gluing_universes_quote | apply gluing_universes_coherent |
      exact Hwk | exact HC | apply gluing_sub_weaken | exact HCg].
Qed.

Lemma gluing_code_instance : forall k Γ A B X i,
    i < k -> wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ i) B ->
    wf_exp Γ A X ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (a_typ i) B ->
    typing_respects_gluing (gluing_universes k) Γ A X ->
    code_respects_gluing k Γ (a_sub B (a_extend a_id X)).
Proof.
  intros k Γ A B X i Hk HA HB HX HBg HXg.
  pose proof (instantiate_type _ _ _ _ HA HX) as Ht.
  exists i; split; [exact Hk |]. split; [exact (substitute_type _ _ _ _ _ Ht HB) |].
  eapply gluing_type_substitution; [apply gluing_universes_quote | apply gluing_universes_coherent |
    exact Ht | exact HB | | exact HBg].
  eapply gluing_instantiation; [apply gluing_universes_quote | apply gluing_universes_coherent |
    exact HA | exact HX | exact HXg].
Qed.

Definition natural_eliminator_respects_gluing :=
  forall k Γ i A Z Suc M,
    0 < k -> i < k ->
    wf_exp (a_nat :: Γ) (a_typ i) A ->
    wf_exp Γ (a_sub A (a_extend a_id a_zero)) Z ->
    wf_exp (A :: a_nat :: Γ) (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc ->
    wf_exp Γ a_nat M ->
    typing_respects_gluing (gluing_universes k) (a_nat :: Γ) (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) Γ (a_sub A (a_extend a_id a_zero)) Z ->
    typing_respects_gluing (gluing_universes k) (A :: a_nat :: Γ)
      (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc ->
    typing_respects_gluing (gluing_universes k) Γ a_nat M ->
    typing_respects_gluing (gluing_universes k) Γ (a_sub A (a_extend a_id M)) (a_natrec A Z Suc M).

Lemma gluing_equality_instantiation : forall U Γ i A X Y P,
    universe_invariants U -> universe_coherence U ->
    wf_exp Γ (a_typ i) A ->
    wf_exp Γ A X -> wf_exp Γ A Y -> wf_exp Γ (a_eq A X Y) P ->
    typing_respects_gluing U Γ A X -> typing_respects_gluing U Γ A Y ->
    typing_respects_gluing U Γ (a_eq A X Y) P ->
    substitution_respects_gluing U Γ (equality_context Γ A)
      (a_extend (a_extend (a_extend a_id X) Y) P).
Proof.
  intros U Γ i A X Y P HU HC HA HX HY HP HXg HYg HPg.
  destruct (equality_instantiation_types _ _ _ _ _ HA HX HY) as (HAW & HEq & HAe & HEqe).
  pose proof (instantiate_type _ _ _ _ HA HX) as HS.
  pose proof (substitute_type _ _ _ _ _ HS HAW) as HAW'.
  pose proof (convert_expression _ _ _ _ _ HY HAW' (wf_exp_eq_sym _ _ _ _ HAe)) as HY'.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HAW HY') as HSS.
  pose proof (substitute_type _ _ _ _ _ HSS HEq) as HEq'.
  pose proof (convert_expression _ _ _ _ _ HP HEq' (wf_exp_eq_sym _ _ _ _ HEqe)) as HP'.
  unfold equality_context.
  eapply gluing_sub_extend; [exact HU | exact HC | exact HSS | exact HEq | exact HP' | |].
  - eapply gluing_sub_extend; [exact HU | exact HC | exact HS | exact HAW | exact HY' | |].
    + exact (gluing_instantiation _ _ _ _ _ HU HC HA HX HXg).
    + eapply gluing_convert_type; [exact HU | exact HC | exact HAW' | exact (wf_exp_eq_sym _ _ _ _ HAe) | exact HYg].
  - eapply gluing_convert_type; [exact HU | exact HC | exact HEq' | exact (wf_exp_eq_sym _ _ _ _ HEqe) | exact HPg].
Qed.

Lemma gluing_equality_result_code : forall k Γ i j A B X Y P,
    j < k ->
    wf_exp Γ (a_typ i) A -> wf_exp Γ A X -> wf_exp Γ A Y -> wf_exp Γ (a_eq A X Y) P ->
    wf_exp (equality_context Γ A) (a_typ j) B ->
    typing_respects_gluing (gluing_universes k) Γ A X ->
    typing_respects_gluing (gluing_universes k) Γ A Y ->
    typing_respects_gluing (gluing_universes k) Γ (a_eq A X Y) P ->
    typing_respects_gluing (gluing_universes k) (equality_context Γ A) (a_typ j) B ->
    code_respects_gluing k Γ (equality_result_type B X Y P).
Proof.
  intros k Γ i j A B X Y P Hk HA HX HY HP HB HXg HYg HPg HBg.
  pose proof (equality_motive_substitution _ _ _ _ _ _ HA HX HY HP) as HS.
  exists j; split; [exact Hk |]. split; [exact (substitute_type _ _ _ _ _ HS HB) |].
  eapply gluing_type_substitution; [apply gluing_universes_quote | apply gluing_universes_coherent |
    exact HS | exact HB | | exact HBg].
  eapply gluing_equality_instantiation;
    [apply gluing_universes_quote | apply gluing_universes_coherent | exact HA | exact HX | exact HY |
      exact HP | exact HXg | exact HYg | exact HPg].
Qed.

Definition equality_eliminator_respects_gluing :=
  forall k Γ i j A B BR X Y P,
    i < k -> j < k ->
    wf_exp Γ (a_typ i) A -> wf_exp Γ A X -> wf_exp Γ A Y ->
    wf_exp (equality_context Γ A) (a_typ j) B ->
    wf_exp (A :: Γ) (equality_branch_type A B) BR ->
    wf_exp Γ (a_eq A X Y) P ->
    typing_respects_gluing (gluing_universes k) Γ (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) Γ A X ->
    typing_respects_gluing (gluing_universes k) Γ A Y ->
    typing_respects_gluing (gluing_universes k) (equality_context Γ A) (a_typ j) B ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (equality_branch_type A B) BR ->
    typing_respects_gluing (gluing_universes k) Γ (a_eq A X Y) P ->
    typing_respects_gluing (gluing_universes k) Γ (equality_result_type B X Y P) (a_eqrec A B BR X Y P).

Definition at_sufficiently_large_universes (P : nat -> Prop) :=
  exists bound, forall k, bound < k -> P k.

Ltac gluing_bound_contains n b :=
  first [constr_eq n b | lazymatch b with Nat.max ?l ?r => first [gluing_bound_contains n l | gluing_bound_contains n r] end].

Ltac gluing_pick_bound b :=
  match goal with
  | n : nat |- _ =>
      tryif gluing_bound_contains n b then fail
      else let c := constr:(Nat.max n b) in gluing_pick_bound c
  | _ => exists (S (S b))
  end.

Ltac gluing_open_eventual :=
  unfold at_sufficiently_large_universes in *;
  repeat match goal with
  | H : exists bound : nat, forall k : nat, bound < k -> _ |- _ =>
      let b := fresh "bound" in destruct H as (b & H)
  end;
  gluing_pick_bound O;
  let k := fresh "k" in let Hk := fresh "Hbound" in intros k Hk;
  repeat match goal with
  | H : forall l : nat, ?b < l -> _ |- _ =>
      specialize (H k ltac:(lia))
  end.

Lemma gluing_code_literal : forall k Γ i,
    wf_ctx Γ -> S i < k -> code_respects_gluing k Γ (a_typ i).
Proof.
  intros k Γ i HΓ Hk. exists (S i); split; [exact Hk |].
  split; [now apply wf_typ | now apply gluing_type_literal].
Qed.

Lemma fundamental_gluing_from_eliminators :
  natural_eliminator_respects_gluing ->
  equality_eliminator_respects_gluing ->
  (forall Γ, wf_ctx Γ ->
    at_sufficiently_large_universes (fun k => gluing_context_valid k Γ)) /\
  (forall Γ Δ, wf_ctx_sub Γ Δ ->
    at_sufficiently_large_universes (fun k => context_inclusion_respects_gluing (gluing_universes k) Γ Δ)) /\
  (forall Γ A M, wf_exp Γ A M ->
    at_sufficiently_large_universes (fun k => gluing_typing_valid k Γ A M)) /\
  (forall Γ Δ σ, wf_sub Γ Δ σ ->
    at_sufficiently_large_universes (fun k => substitution_respects_gluing (gluing_universes k) Γ Δ σ)) /\
  (forall Γ A B, wf_subtyp Γ A B ->
    at_sufficiently_large_universes (fun k => subtype_respects_gluing (gluing_universes k) Γ A B)).
Proof.
  intros Hnat Heq.
  assert (Hfund :
    (forall Γ, wf_ctx Γ ->
      at_sufficiently_large_universes (fun k => gluing_context_valid k Γ)) /\
    (forall Γ Δ, wf_ctx_sub Γ Δ ->
      at_sufficiently_large_universes (fun k => context_inclusion_respects_gluing (gluing_universes k) Γ Δ)) /\
    (forall Γ A M, wf_exp Γ A M ->
      at_sufficiently_large_universes (fun k => gluing_typing_valid k Γ A M)) /\
    (forall Γ A M N, wf_exp_eq Γ A M N -> True) /\
    (forall Γ Δ σ, wf_sub Γ Δ σ ->
      at_sufficiently_large_universes (fun k => substitution_respects_gluing (gluing_universes k) Γ Δ σ)) /\
    (forall Γ Δ σ τ, wf_sub_eq Γ Δ σ τ -> True) /\
    (forall Γ A B, wf_subtyp Γ A B ->
      at_sufficiently_large_universes (fun k => subtype_respects_gluing (gluing_universes k) Γ A B))).
  {
    apply syntactic_wf_mut_ind; intros; try exact I; gluing_open_eventual.
    all: repeat match goal with H : gluing_typing_valid _ _ _ _ |- _ => destruct H as [H ?] end.
    - apply gluing_context_empty.
    - eapply gluing_context_extend; [|eassumption..]; lia.
    - unfold context_inclusion_respects_gluing; auto.
    - eapply gluing_context_inclusion_extend; eassumption.
    - split; [apply gluing_type_literal; lia |].
      eapply gluing_code_literal; [assumption | lia].
    - split; [apply gluing_natural_code; lia |].
      eapply gluing_code_literal; [assumption | lia].
    - split; [apply gluing_zero |].
      exists 0; split; [lia |]. split; [now apply wf_nat | apply gluing_natural_code; lia].
    - split; [apply gluing_succ; [apply gluing_universes_quote | apply gluing_universes_coherent | assumption..] | assumption].
    - split; [eapply Hnat; [| |eassumption..]; lia |].
      eapply gluing_code_instance;
        [ | | eassumption | eassumption | eassumption | eassumption].
      + lia.
      + eapply cumulative_type; [apply wf_nat; eapply expression_context; eassumption | lia].
    - split; [eapply gluing_pi; [|eassumption..]; lia |].
      eapply gluing_code_literal; [eapply expression_context; eassumption | lia].
    - match goal with
      | HA : wf_exp ?Γ (a_typ ?i) ?A,
        HM : wf_exp (?A :: ?Γ) ?B ?M,
        HAg : typing_respects_gluing (gluing_universes ?k) ?Γ (a_typ ?i) ?A,
        HMg : typing_respects_gluing (gluing_universes ?k) (?A :: ?Γ) ?B ?M,
        HC : code_respects_gluing ?k (?A :: ?Γ) ?B |- _ =>
        destruct HC as (j & Hj & HB & HBg);
        let l := constr:(Nat.max i j) in
        assert (Hl : l < k) by lia;
        let HAl := fresh "HAl" in let HBl := fresh "HBl" in
        let HAlg := fresh "HAlg" in let HBlg := fresh "HBlg" in
        pose proof (cumulative_type _ _ _ l HA (Nat.le_max_l i j)) as HAl;
        pose proof (cumulative_type _ _ _ l HB (Nat.le_max_r i j)) as HBl;
        pose proof (gluing_cumulativity k _ _ _ _ (Nat.le_max_l i j) Hl HAg) as HAlg;
        pose proof (gluing_cumulativity k _ _ _ _ (Nat.le_max_r i j) Hl HBg) as HBlg;
        split; [exact (gluing_function _ _ _ _ _ _ Hl HAl HBl HM HAlg HBlg HMg) |];
        exists l; split; [exact Hl |]; split; [exact (wf_pi _ _ _ _ HAl HBl) | exact (gluing_pi _ _ _ _ _ Hl HAl HBl HAlg HBlg)]
      end.
    - split; [eapply gluing_application; [|eassumption..]; lia |].
      eapply gluing_code_instance; [|eassumption..]; lia.
    - split; [eapply gluing_sigma; [|eassumption..]; lia |].
      eapply gluing_code_literal; [eapply expression_context; eassumption | lia].
    - split; [eapply gluing_pair; [|eassumption..]; lia |].
      eexists; split; [|split; [eapply wf_sigma; eassumption | eapply gluing_sigma; [|eassumption..]; lia]]; lia.
    - split.
      + match goal with
        | HA : wf_exp ?Γ (a_typ ?i) ?A,
          HB : wf_exp (?A :: ?Γ) (a_typ ?i) ?B,
          HM : wf_exp ?Γ (a_sigma ?A ?B) ?M,
          HAg : typing_respects_gluing (gluing_universes ?k) ?Γ (a_typ ?i) ?A,
          HBg : typing_respects_gluing (gluing_universes ?k) (?A :: ?Γ) (a_typ ?i) ?B,
          HMg : typing_respects_gluing (gluing_universes ?k) ?Γ (a_sigma ?A ?B) ?M |- _ =>
          exact (proj1 (gluing_projections k Γ i A B M ltac:(lia) HA HB HM HAg HBg HMg))
        end.
      + eexists; split; [|split; eassumption]; lia.
    - match goal with
      | HA : wf_exp ?Γ (a_typ ?i) ?A,
        HB : wf_exp (?A :: ?Γ) (a_typ ?i) ?B,
        HM : wf_exp ?Γ (a_sigma ?A ?B) ?M,
        HAg : typing_respects_gluing (gluing_universes ?k) ?Γ (a_typ ?i) ?A,
        HBg : typing_respects_gluing (gluing_universes ?k) (?A :: ?Γ) (a_typ ?i) ?B,
        HMg : typing_respects_gluing (gluing_universes ?k) ?Γ (a_sigma ?A ?B) ?M |- _ =>
        destruct (gluing_projections k Γ i A B M ltac:(lia) HA HB HM HAg HBg HMg) as (Hfst & Hsnd);
        split; [exact Hsnd |];
        eapply gluing_code_instance; [| exact HA | exact HB | exact (wf_fst _ _ _ _ _ HA HB HM) | exact HBg | exact Hfst]; lia
      end.
    - split.
      + eapply gluing_var; [apply gluing_universes_quote | apply gluing_universes_coherent | eassumption].
      + match goal with Hctx : gluing_context_valid _ _, Hl : ctx_lookup _ _ _ |- _ =>
          exact (proj2 Hctx _ _ Hl) end.
    - split; [eapply gluing_equality; [|eassumption..]; lia |].
      eapply gluing_code_literal; [eapply expression_context; eassumption | lia].
    - split; [eapply gluing_reflexivity; [|eassumption..]; lia |].
      eexists; split; [|split; [eapply wf_eq; eassumption | eapply gluing_equality; [|eassumption..]; lia]]; lia.
    - split.
      + eapply Heq; [| |eassumption..]; lia.
      + eapply gluing_equality_result_code; [|eassumption..]; lia.
    - split.
      + eapply gluing_exp_sub; [apply gluing_universes_quote | apply gluing_universes_coherent | eassumption..].
      + match goal with H : code_respects_gluing _ _ _ |- _ => destruct H as (i & Hi & HA & HAg) end.
        exists i; split; [exact Hi |]. split; [eapply substitute_type; eassumption |].
        eapply gluing_type_substitution; [apply gluing_universes_quote | apply gluing_universes_coherent | eassumption..].
    - split.
      + eapply gluing_exp_subtype; eassumption.
      + eexists; split; [|split; eassumption]; lia.
    - apply gluing_sub_id; [apply gluing_universes_quote | apply gluing_universes_coherent].
    - apply gluing_sub_weaken.
    - eapply gluing_sub_compose; [apply gluing_universes_quote | apply gluing_universes_coherent | eassumption..].
    - eapply gluing_sub_extend; [apply gluing_universes_quote | apply gluing_universes_coherent | eassumption..].
    - eapply gluing_sub_context_inclusion; eassumption.
    - eapply gluing_subtype_conversion; [apply gluing_universes_quote | apply gluing_universes_coherent | eassumption..].
    - eapply gluing_subtype_trans; eassumption.
    - apply gluing_subtype_universe; lia.
    - eapply gluing_subtype_pi; [|eassumption..]; lia.
    - eapply gluing_subtype_sigma; [|eassumption..]; lia.
  }
  tauto.
Qed.


Lemma lift_glued_environment_natural : forall k Γ Θ σ ρ,
    glued_environment (gluing_universes k) Θ Γ σ ρ ->
    glued_environment (gluing_universes k) (a_nat :: Θ) (a_nat :: Γ) (Syntax.q σ)
      (extend_env ρ (d_neut d_nat (d_var (length Θ)))).
Proof.
  intros k Γ Θ σ ρ HE.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  destruct (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  eapply lift_glued_environment_as.
  - apply gluing_universes_quote.
  - apply gluing_universes_coherent.
  - apply gluing_universes_weaken.
  - exact HE.
  - exact (wf_nat _ HΓ).
  - apply eval_exp_nat.
  - exact (glued_type_nat _ _ HΘ).
  - apply wf_exp_eq_sym; exact (wf_exp_eq_nat_sub _ _ _ HS).
Qed.

Lemma natural_glued_motive : forall k Γ Θ σ ρ i A X x,
    i < k -> glued_environment (gluing_universes k) Θ Γ σ ρ ->
    typing_respects_gluing (gluing_universes k) (a_nat :: Γ) (a_typ i) A ->
    glued_term (gluing_universes k) Θ a_nat X d_nat x ->
    exists b R, eval_exp A (extend_env ρ x) b /\
      glued_type (gluing_universes k) Θ i (a_sub A (a_extend σ X)) b R.
Proof.
  intros k Γ Θ σ ρ i A X x Hk HE HAg GX.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  destruct (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  pose proof (wf_nat _ HΓ) as HNat.
  pose proof (substitute_type _ _ _ _ _ HS HNat) as HNs.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GX HNs
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS))) as GX'.
  eapply extract_glued_code; [exact Hk | | exact HAg].
  eapply glued_environment_extend;
    [apply gluing_universes_quote | apply gluing_universes_coherent | exact HE | exact HNat | apply eval_exp_nat | exact GX'].
Qed.

Lemma soundness_from_eliminators :
    natural_eliminator_respects_gluing ->
    equality_eliminator_respects_gluing ->
    forall Γ M A, wf_exp Γ A M -> exists W, nbe Γ M A W /\ wf_exp_eq Γ A M W.
Proof.
  intros Hnat Heq Γ M A HM.
  destruct (fundamental_gluing_from_eliminators Hnat Heq) as (Hctx & _ & Hterm & _).
  destruct (Hctx _ (expression_context _ _ _ HM)) as (bc & HC).
  destruct (Hterm _ _ _ HM) as (bt & HT).
  set (k := S (Nat.max bc bt)).
  destruct (HC k ltac:(unfold k; lia)) as (Henv & _).
  destruct (HT k ltac:(unfold k; lia)) as (HG & _).
  exact (gluing_implies_soundness _ _ _ _ (gluing_universes_quote k)
    (gluing_universes_coherent k) HM Henv HG).
Qed.

Lemma natural_glued_argument : forall U Γ Θ σ ρ X x,
    universe_invariants U -> universe_coherence U ->
    glued_environment U Θ Γ σ ρ ->
    glued_term U Θ a_nat X d_nat x ->
    glued_environment U Θ (a_nat :: Γ) (a_extend σ X) (extend_env ρ x).
Proof.
  intros U Γ Θ σ ρ X x HU HC HE GX.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (wf_nat _ (proj2 (substitution_contexts _ _ _ HS))) as HNat.
  pose proof (substitute_type _ _ _ _ _ HS HNat) as HNs.
  eapply glued_environment_extend;
    [exact HU | exact HC | exact HE | exact HNat | apply eval_exp_nat |].
  exact (glued_term_type_change _ _ _ _ _ _ _ _ GX HNs (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS))).
Qed.

Lemma natural_zero_branch_type : forall Γ Θ i A σ,
    wf_sub Θ Γ σ -> wf_exp (a_nat :: Γ) (a_typ i) A ->
    wf_exp_eq Θ (a_typ i) (a_sub (a_sub A (a_extend a_id a_zero)) σ)
      (a_sub A (a_extend σ a_zero)).
Proof.
  intros Γ Θ i A σ HS HA.
  destruct (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  pose proof (wf_nat _ HΓ) as HN.
  pose proof (wf_zero _ HΓ) as HZ.
  pose proof (wf_zero _ HΘ) as HZt.
  pose proof (substitute_type _ _ _ _ _ HS HN) as HNs.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS)) as HNE.
  pose proof (convert_expression _ _ _ _ _ HZt HNs HNE) as HZt'.
  pose proof (wf_exp_sub _ _ _ _ _ HS HZ) as HZs.
  pose proof (convert_equality _ _ _ _ _ _ (wf_exp_eq_zero_sub _ _ _ HS) HNs HNE) as HZE.
  pose proof (substitute_instantiated_type _ _ _ _ _ _ _ _ HS HN HA HZ) as HAE.
  eapply wf_exp_eq_trans; [exact HAE |].
  exact (type_extension_congruence _ _ _ _ _ _ _ _ _ _ HS HN HA (reflexive_substitution _ _ _ HS) HZs HZE).
Qed.

Lemma natural_glued_zero_branch : forall k Γ Θ i A Z σ ρ,
    glued_environment (gluing_universes k) Θ Γ σ ρ ->
    wf_exp (a_nat :: Γ) (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) Γ (a_sub A (a_extend a_id a_zero)) Z ->
    exists b z,
      eval_exp A (extend_env ρ d_zero) b /\ eval_exp Z ρ z /\
      glued_term (gluing_universes k) Θ (a_sub A (a_extend σ a_zero)) (a_sub Z σ) b z.
Proof.
  intros k Γ Θ i A Z σ ρ HE HA HZ.
  destruct (HZ _ _ _ HE) as (b & z & Hb & Hz & GZ).
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  destruct (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  pose proof (wf_nat _ HΓ) as HN.
  pose proof (substitute_type _ _ _ _ _ HS HN) as HNs.
  pose proof (convert_expression _ _ _ _ _ (wf_zero _ HΘ) HNs
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS))) as Ht.
  pose proof (substitute_type _ _ _ _ _ (wf_sub_extend _ _ _ _ _ _ HS HN Ht) HA) as HT.
  assert (Hb' : eval_exp A (extend_env ρ d_zero) b).
  {
    inversion Hb; subst.
    assert (Hzero : eval_sub (a_extend a_id a_zero) ρ (extend_env ρ d_zero))
      by (apply eval_sub_extend; [apply eval_sub_id | apply eval_exp_zero]).
    resolve_eval. assumption.
  }
  exists b, z; split; [exact Hb' |]. split; [exact Hz |].
  exact (glued_term_type_change _ _ _ _ _ _ _ _ GZ HT (natural_zero_branch_type _ _ _ _ _ HS HA)).
Qed.

Lemma substitute_two_extensions_projection : forall Γ Θ i j A B σ X Y,
    wf_sub Θ Γ σ -> wf_exp Γ (a_typ i) A -> wf_exp (A :: Γ) (a_typ j) B ->
    wf_exp Θ (a_sub A σ) X -> wf_exp Θ (a_sub B (a_extend σ X)) Y ->
    wf_sub_eq Θ Γ (a_compose (a_compose a_weaken a_weaken) (a_extend (a_extend σ X) Y)) σ.
Proof.
  intros Γ Θ i j A B σ X Y HS HA HB HX HY.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HX) as HSX.
  pose proof (wf_sub_extend _ _ _ _ _ _ HSX HB HY) as HSXY.
  pose proof (wf_sub_weaken _ _ (proj2 (substitution_contexts _ _ _ HSX))) as Hwk.
  pose proof (wf_sub_weaken _ _ (proj2 (substitution_contexts _ _ _ HSXY))) as Hwk'.
  eapply wf_sub_eq_trans;
    [exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ Hwk Hwk' HSXY) |].
  eapply wf_sub_eq_trans; [|exact (wf_sub_eq_p_extend _ _ _ _ _ _ HS HA HX)].
  eapply wf_sub_eq_compose_cong;
    [exact (wf_sub_eq_p_extend _ _ _ _ _ _ HSX HB HY) | now apply reflexive_substitution].
Qed.

Lemma natural_second_variable : forall Γ A i,
    wf_exp (a_nat :: Γ) (a_typ i) A ->
    wf_exp (A :: a_nat :: Γ) a_nat (a_var 1).
Proof.
  intros Γ A i HA.
  pose proof (expression_context _ _ _ HA) as HΓ.
  pose proof (wf_ctx_extend _ _ _ HΓ HA) as HΓA.
  pose proof (wf_sub_weaken _ _ HΓ) as HW.
  pose proof (wf_sub_weaken _ _ HΓA) as HW'.
  pose proof (wf_vlookup _ _ _ HΓA (there _ _ _ _ (here a_nat Γ))) as Hx.
  eapply convert_expression; [exact Hx | exact (wf_nat _ HΓA) |].
  eapply wf_exp_eq_trans.
  - apply wf_exp_eq_sym. eapply type_substitution_compose; [exact HW' | exact HW |].
    apply wf_nat; exact (proj2 (substitution_contexts _ _ _ HW)).
  - exact (wf_exp_eq_nat_sub _ _ _ (wf_sub_compose _ _ _ _ _ HW' HW)).
Qed.

Lemma natural_step_branch_type : forall Γ Θ i A σ X Y,
    wf_sub Θ Γ σ -> wf_exp (a_nat :: Γ) (a_typ i) A ->
    wf_exp Θ a_nat X -> wf_exp Θ (a_sub A (a_extend σ X)) Y ->
    wf_exp (A :: a_nat :: Γ) (a_typ i)
      (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) /\
    wf_exp_eq Θ (a_typ i)
      (a_sub (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) (a_extend (a_extend σ X) Y))
      (a_sub A (a_extend σ (a_succ X))).
Proof.
  intros Γ Θ i A σ X Y HS HA HX HY.
  destruct (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  pose proof (wf_nat _ HΓ) as HNat.
  pose proof (substitute_type _ _ _ _ _ HS HNat) as HNs.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS)) as HNE.
  pose proof (convert_expression _ _ _ _ _ HX HNs HNE) as HX'.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HNat HX') as HSX.
  pose proof (wf_sub_extend _ _ _ _ _ _ HSX HA HY) as HSXY.
  pose proof (proj2 (substitution_contexts _ _ _ HSX)) as HΓN.
  pose proof (proj2 (substitution_contexts _ _ _ HSXY)) as HΓNA.
  pose proof (wf_sub_compose _ _ _ _ _ (wf_sub_weaken _ _ HΓNA) (wf_sub_weaken _ _ HΓN)) as HW2.
  pose proof (natural_second_variable _ _ _ HA) as H1.
  pose proof (wf_succ _ _ H1) as HSucc.
  pose proof (substitute_type _ _ _ _ _ HW2 HNat) as HNw.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HW2)) as HNwe.
  pose proof (convert_expression _ _ _ _ _ HSucc HNw HNwe) as HSucc'.
  pose proof (wf_sub_extend _ _ _ _ _ _ HW2 HNat HSucc') as Hbranch.
  pose proof (substitute_type _ _ _ _ _ Hbranch HA) as HT.
  split; [exact HT |].
  pose proof (wf_sub_compose _ _ _ _ _ HSXY HW2) as HC.
  pose proof (substitute_type _ _ _ _ _ HC HNat) as HNcomp.
  assert (HXe : wf_exp_eq Θ a_nat (a_sub (a_var 1) (a_extend (a_extend σ X) Y)) X).
  {
    pose proof (wf_sub_eq_p_extend _ _ _ _ _ _ HS HNat HX') as Hproj.
    pose proof (wf_sub_compose _ _ _ _ _ HSX (wf_sub_weaken _ _ HΓN)) as Hwkx.
    assert (Htyp : wf_exp_eq Θ (a_typ 0) (a_sub (a_sub a_nat a_weaken) (a_extend σ X)) a_nat).
    {
      eapply wf_exp_eq_trans; [|exact (wf_exp_eq_nat_sub _ _ _ HS)].
      eapply wf_exp_eq_trans.
      - apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HSX (wf_sub_weaken _ _ HΓN) HNat).
      - eapply substitute_type_equality; [exact Hwkx | exact Hproj | now apply reflexive_expression].
    }
    eapply wf_exp_eq_trans.
    - eapply convert_equality; [exact (wf_exp_eq_var_S_sub _ _ _ _ _ _ _ _ HSX HA HY (here a_nat Γ)) | exact (wf_nat _ HΘ) | exact Htyp].
    - eapply convert_equality; [exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ HS HNat HX') | exact (wf_nat _ HΘ) | exact (wf_exp_eq_nat_sub _ _ _ HS)].
  }
  assert (HSE : wf_exp_eq Θ a_nat (a_sub (a_succ (a_var 1)) (a_extend (a_extend σ X) Y)) (a_succ X)).
  { exact (wf_exp_eq_trans _ _ _ _ _ (wf_exp_eq_succ_sub _ _ _ _ HSXY H1) (wf_exp_eq_succ_cong _ _ _ HXe)). }
  pose proof (convert_equality _ _ _ _ _ _ HSE HNcomp (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HC))) as HSEC.
  pose proof (wf_exp_sub _ _ _ _ _ HSXY HSucc') as HSC.
  pose proof (convert_expression _ _ _ _ _ HSC HNcomp (wf_exp_eq_sym _ _ _ _
      (type_substitution_compose _ _ _ _ _ _ _ HSXY HW2 HNat))) as HSC'.
  pose proof (substitute_two_extensions_projection _ _ _ _ _ _ _ _ _ HS HNat HA HX' HY) as Hproj.
  eapply wf_exp_eq_trans.
  - apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HSXY Hbranch HA).
  - eapply wf_exp_eq_trans.
    + eapply substitute_type_equality;
        [exact (wf_sub_compose _ _ _ _ _ HSXY Hbranch) | exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ HW2 HNat HSucc' HSXY)
        | now apply reflexive_expression].
    + exact (type_extension_congruence _ _ _ _ _ _ _ _ _ _ HC HNat HA Hproj HSC' HSEC).
Qed.

Lemma natural_glued_successor_branch : forall k Γ Θ i A Suc σ ρ X x Y y b,
    glued_environment (gluing_universes k) Θ Γ σ ρ ->
    wf_exp (a_nat :: Γ) (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) (A :: a_nat :: Γ)
      (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc ->
    glued_term (gluing_universes k) Θ a_nat X d_nat x ->
    eval_exp A (extend_env ρ x) b ->
    glued_term (gluing_universes k) Θ (a_sub A (a_extend σ X)) Y b y ->
    exists c z,
      eval_exp A (extend_env ρ (d_succ x)) c /\
      eval_exp Suc (extend_env (extend_env ρ x) y) z /\
      glued_term (gluing_universes k) Θ (a_sub A (a_extend σ (a_succ X)))
        (a_sub Suc (a_extend (a_extend σ X) Y)) c z.
Proof.
  intros k Γ Θ i A Suc σ ρ X x Y y b HE HA Hstep GX Hb GY.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (natural_glued_argument _ _ _ _ _ _ _ HU HC HE GX) as HE'.
  pose proof (glued_environment_extend _ _ _ _ _ _ _ _ _ _ HU HC HE' HA Hb GY) as HE''.
  destruct (Hstep _ _ _ HE'') as (c & z & Hc & Hz & GZ).
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (glued_term_typing _ _ _ _ _ _ GX) as HX.
  pose proof (glued_term_typing _ _ _ _ _ _ GY) as HY.
  destruct (natural_step_branch_type _ _ _ _ _ _ _ HS HA HX HY) as (HT & HTE).
  destruct (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  pose proof (wf_nat _ HΓ) as HN.
  pose proof (substitute_type _ _ _ _ _ HS HN) as HNs.
  pose proof (convert_expression _ _ _ _ _ (wf_succ _ _ HX) HNs
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS))) as HXt.
  pose proof (substitute_type _ _ _ _ _ (wf_sub_extend _ _ _ _ _ _ HS HN HXt) HA) as HTs.
  assert (Hc' : eval_exp A (extend_env ρ (d_succ x)) c).
  {
    inversion Hc; subst.
    assert (He : eval_sub (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))
        (extend_env (extend_env ρ x) y) (extend_env ρ (d_succ x))).
    { eapply eval_sub_extend.
      - eapply eval_sub_compose; apply eval_sub_weaken.
      - apply eval_exp_succ, eval_exp_var. }
    resolve_eval. assumption.
  }
  exists c, z; split; [exact Hc' |]. split; [exact Hz |].
  exact (glued_term_type_change _ _ _ _ _ _ _ _ GZ HTs HTE).
Qed.

Lemma lift_substitution_as_data : forall Γ Θ A D σ i,
    wf_sub Θ Γ σ -> wf_exp Γ (a_typ i) A -> wf_exp Θ (a_typ i) D ->
    wf_exp_eq Θ (a_typ i) D (a_sub A σ) ->
    let st := a_compose σ a_weaken in
    wf_sub (D :: Θ) Γ st /\
    wf_exp (D :: Θ) (a_sub A st) (a_var 0) /\
    wf_sub (D :: Θ) (A :: Γ) (Syntax.q σ) /\
    wf_sub_eq (D :: Θ) Γ (a_compose a_weaken (Syntax.q σ)) st.
Proof.
  intros Γ Θ A D σ i HS HA HD HE; cbn zeta.
  pose proof (wf_ctx_extend _ _ _ (expression_context _ _ _ HD) HD) as Hctx.
  pose proof (wf_sub_weaken _ _ Hctx) as Hwk.
  pose proof (wf_sub_compose _ _ _ _ _ Hwk HS) as HSW.
  pose proof (substitute_type _ _ _ _ _ HSW HA) as HAT.
  assert (HDE : wf_exp_eq (D :: Θ) (a_typ i) (a_sub D a_weaken) (a_sub A (a_compose σ a_weaken))).
  {
    eapply wf_exp_eq_trans;
      [eapply substitute_type_equality; [exact Hwk | now apply reflexive_substitution | exact HE] |].
    apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ Hwk HS HA).
  }
  pose proof (convert_expression _ _ _ _ _ (type_of_first_variable _ _ Hctx) HAT HDE) as Hvar.
  split; [exact HSW |]. split; [exact Hvar |].
  split; [exact (wf_sub_extend _ _ _ _ _ _ HSW HA Hvar) | exact (wf_sub_eq_p_extend _ _ _ _ _ _ HSW HA Hvar)].
Qed.

Lemma lift_substitution_natural_data : forall Γ Θ σ,
    wf_sub Θ Γ σ ->
    wf_sub (a_nat :: Θ) (a_nat :: Γ) (Syntax.q σ) /\
    wf_sub_eq (a_nat :: Θ) Γ (a_compose a_weaken (Syntax.q σ)) (a_compose σ a_weaken) /\
    wf_exp_eq (a_nat :: Θ) a_nat (a_sub (a_var 0) (Syntax.q σ)) (a_var 0).
Proof.
  intros Γ Θ σ HS.
  destruct (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  pose proof (wf_nat _ HΓ) as HN.
  pose proof (wf_nat _ HΘ) as HNt.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS)) as HNE.
  destruct (lift_substitution_as_data _ _ _ _ _ _ HS HN HNt HNE) as (HsW & H0 & HQ & HE).
  split; [exact HQ |]. split; [exact HE |].
  exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_var_0_sub _ _ _ _ _ _ HsW HN H0)
    (wf_nat _ (proj1 (substitution_contexts _ _ _ HQ))) (wf_exp_eq_nat_sub _ _ _ HsW)).
Qed.

Lemma natural_lift_instance_type : forall Γ Θ i A σ X,
    wf_sub Θ Γ σ -> wf_exp (a_nat :: Γ) (a_typ i) A -> wf_exp Θ a_nat X ->
    wf_exp_eq Θ (a_typ i) (a_sub (a_sub A (Syntax.q σ)) (a_extend a_id X))
      (a_sub A (a_extend σ X)).
Proof.
  intros Γ Θ i A σ X HS HA HZ.
  destruct (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  destruct (lift_substitution_natural_data _ _ _ HS) as (HQ & _).
  pose proof (wf_nat _ HΓ) as HN.
  pose proof (wf_nat _ HΘ) as HNt.
  pose proof (instantiate_type _ _ _ _ HNt HZ) as HZI.
  pose proof (wf_sub_id _ HΘ) as HID.
  pose proof (wf_sub_compose _ _ _ _ _ HID HS) as HSI.
  pose proof (substitute_type _ _ _ _ _ HSI HN) as HNsi.
  pose proof (convert_expression _ _ _ _ _ HZ HNsi (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HSI))) as HZi.
  destruct (typed_lift_instantiation _ _ _ _ _ _ _ _ HID HS HN HZi) as (HL & HLE).
  eapply wf_exp_eq_trans.
  - apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HZI HQ HA).
  - eapply wf_exp_eq_trans.
    + eapply substitute_type_equality;
        [exact (wf_sub_compose _ _ _ _ _ HZI HQ) | exact HLE | now apply reflexive_expression].
    + exact (type_extension_congruence _ _ _ _ _ _ _ _ _ _ HSI HN HA
        (wf_sub_eq_id_compose_left _ _ _ HS) HZi (reflexive_expression _ _ _ HZi)).
Qed.

Lemma weaken_zero_substitution : forall Γ Θ i A σ,
    wf_sub Θ Γ σ -> wf_exp (a_nat :: Γ) (a_typ i) A ->
    wf_exp_eq Θ (a_typ i) (a_sub (a_sub A (Syntax.q σ)) (a_extend a_id a_zero))
      (a_sub A (a_extend σ a_zero)).
Proof.
  intros Γ Θ i A σ HS HA.
  exact (natural_lift_instance_type _ _ _ _ _ _ HS HA (wf_zero _ (proj1 (substitution_contexts _ _ _ HS)))).
Qed.

Lemma natural_step_lift_data : forall Γ Θ i A σ,
    wf_sub Θ Γ σ -> wf_exp (a_nat :: Γ) (a_typ i) A ->
    let A' := a_sub A (Syntax.q σ) in
    let HH := a_compose a_weaken a_weaken in
    wf_exp (a_nat :: Θ) (a_typ i) A' /\
    wf_sub (A' :: a_nat :: Θ) (A :: a_nat :: Γ) (Syntax.q (Syntax.q σ)) /\
    wf_sub_eq (A' :: a_nat :: Θ) Γ (a_compose HH (Syntax.q (Syntax.q σ))) (a_compose σ HH) /\
    wf_exp_eq (A' :: a_nat :: Θ) a_nat (a_sub (a_var 1) (Syntax.q (Syntax.q σ))) (a_var 1).
Proof.
  intros Γ Θ i A σ HS HA; cbn zeta.
  destruct (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  destruct (lift_substitution_natural_data _ _ _ HS) as (HQ & HQE & H0E).
  pose proof (substitute_type _ _ _ _ _ HQ HA) as HA'.
  destruct (lift_substitution_as_data _ _ _ _ _ _ HQ HA HA' (reflexive_expression _ _ _ HA'))
    as (HqW & H0 & HQQ & HQQE).
  pose proof (wf_sub_weaken _ _ (proj1 (substitution_contexts _ _ _ HQ))) as HWt.
  pose proof (wf_sub_weaken _ _ (proj2 (substitution_contexts _ _ _ HQ))) as HWs.
  pose proof (wf_sub_weaken _ _ (proj1 (substitution_contexts _ _ _ HQQ))) as HWt'.
  pose proof (wf_sub_weaken _ _ (proj2 (substitution_contexts _ _ _ HQQ))) as HWs'.
  split; [exact HA' |]. split; [exact HQQ |]. split.
  - eapply wf_sub_eq_trans;
      [exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HWs HWs' HQQ) |].
    eapply wf_sub_eq_trans.
    + exact (wf_sub_eq_compose_cong _ _ _ _ _ _ _ HQQE (reflexive_substitution _ _ _ HWs)).
    + eapply wf_sub_eq_trans.
      * apply wf_sub_eq_sym; exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HWs HQ HWt').
      * eapply wf_sub_eq_trans.
        -- exact (wf_sub_eq_compose_cong _ _ _ _ _ _ _ (reflexive_substitution _ _ _ HWt') HQE).
        -- exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HS HWt HWt').
  - pose proof (wf_nat _ HΓ) as HN.
    pose proof (wf_nat _ (proj1 (substitution_contexts _ _ _ HQQ))) as HNt.
    pose proof (wf_exp_eq_nat_sub _ _ _ HWs) as HNE.
    pose proof (wf_exp_eq_nat_sub _ _ _ HWt) as HNE'.
    pose proof (type_of_first_variable _ _ (proj2 (substitution_contexts _ _ _ HQ))) as Hx.
    pose proof (type_of_first_variable _ _ (proj1 (substitution_contexts _ _ _ HQ))) as Hx'.
    pose proof (convert_expression _ _ _ _ _ Hx (wf_nat _ (proj2 (substitution_contexts _ _ _ HQ))) HNE) as Hxn.
    assert (Htype : wf_exp_eq (a_sub A (Syntax.q σ) :: a_nat :: Θ) (a_typ 0)
      (a_sub (a_sub a_nat a_weaken) (a_compose (Syntax.q σ) a_weaken)) a_nat).
    {
      eapply wf_exp_eq_trans; [|exact (wf_exp_eq_nat_sub _ _ _ HqW)].
      eapply substitute_type_equality; [exact HqW | now apply reflexive_substitution | exact HNE].
    }
    eapply wf_exp_eq_trans.
    + eapply convert_equality;
        [exact (wf_exp_eq_var_S_sub _ _ _ _ _ _ _ _ HqW HA H0 (here a_nat Γ)) | exact HNt | exact Htype].
    + eapply wf_exp_eq_trans.
      * exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HWt' HQ Hxn)
          HNt (wf_exp_eq_nat_sub _ _ _ HqW)).
      * eapply wf_exp_eq_trans.
        -- exact (convert_equality _ _ _ _ _ _
             (wf_exp_eq_sub_cong _ _ _ _ _ _ _ H0E (reflexive_substitution _ _ _ HWt'))
             HNt (wf_exp_eq_nat_sub _ _ _ HWt')).
        -- exact (convert_equality _ _ _ _ _ _
            (wf_exp_eq_var_weaken _ _ _ _ (proj1 (substitution_contexts _ _ _ HQQ)) (here a_nat Θ))
            HNt (wf_exp_eq_trans _ _ _ _ _
              (substitute_type_equality _ _ _ _ _ _ _ HWt' (reflexive_substitution _ _ _ HWt') HNE')
              (wf_exp_eq_nat_sub _ _ _ HWt'))).
Qed.

Lemma natural_step_index_substitution : forall Γ i A,
    wf_exp (a_nat :: Γ) (a_typ i) A ->
    wf_sub (A :: a_nat :: Γ) (a_nat :: Γ)
      (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1))).
Proof.
  intros Γ i A HA.
  pose proof (expression_context _ _ _ HA) as HΓN.
  pose proof (wf_ctx_extend _ _ _ HΓN HA) as HΓNA.
  pose proof (wf_sub_weaken _ _ HΓN) as HW.
  pose proof (wf_sub_weaken _ _ HΓNA) as HW'.
  pose proof (wf_sub_compose _ _ _ _ _ HW' HW) as HW2.
  pose proof (wf_nat _ (proj2 (substitution_contexts _ _ _ HW2))) as HN.
  eapply wf_sub_extend; [exact HW2 | exact HN |].
  eapply convert_expression.
  - apply wf_succ; exact (natural_second_variable _ _ _ HA).
  - exact (substitute_type _ _ _ _ _ HW2 HN).
  - apply wf_exp_eq_sym; exact (wf_exp_eq_nat_sub _ _ _ HW2).
Qed.

Lemma weaken_step_substitution : forall Γ Θ i A σ,
    wf_sub Θ Γ σ -> wf_exp (a_nat :: Γ) (a_typ i) A ->
    let s := a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)) in
    wf_exp_eq (a_sub A (Syntax.q σ) :: a_nat :: Θ) (a_typ i)
      (a_sub (a_sub A s) (Syntax.q (Syntax.q σ))) (a_sub (a_sub A (Syntax.q σ)) s).
Proof.
  intros Γ Θ i A σ HS HA; cbn zeta.
  destruct (natural_step_lift_data _ _ _ _ _ HS HA) as (HA' & HQQ & Hdbl & Hvar).
  destruct (lift_substitution_natural_data _ _ _ HS) as (HQ & _).
  pose proof (natural_step_index_substitution _ _ _ HA) as HSS.
  pose proof (natural_step_index_substitution _ _ _ HA') as HST.
  pose proof (wf_sub_weaken _ _ (expression_context _ _ _ HA)) as Hwk.
  pose proof (wf_sub_weaken _ _ (expression_context _ _ _ HA')) as Hwk'.
  pose proof (wf_sub_weaken _ _ (proj2 (substitution_contexts _ _ _ HQQ))) as HW.
  pose proof (wf_sub_weaken _ _ (proj1 (substitution_contexts _ _ _ HQQ))) as HW'.
  pose proof (wf_sub_compose _ _ _ _ _ HW Hwk) as HW2.
  pose proof (wf_sub_compose _ _ _ _ _ HW' Hwk') as HW2'.
  pose proof (wf_sub_compose _ _ _ _ _ HQQ HW2) as HW2Q.
  pose proof (wf_sub_compose _ _ _ _ _ HW2' HS) as HW2S.
  pose proof (wf_nat _ (proj2 (substitution_contexts _ _ _ HS))) as HNat.
  pose proof (wf_succ _ _ (natural_second_variable _ _ _ HA)) as Hs.
  pose proof (wf_succ _ _ (natural_second_variable _ _ _ HA')) as Hs'.
  pose proof (convert_expression _ _ _ _ _ Hs (substitute_type _ _ _ _ _ HW2 HNat)
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HW2))) as Hst.
  pose proof (convert_expression _ _ _ _ _ Hs' (substitute_type _ _ _ _ _ HW2S HNat)
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HW2S))) as Hst'.
  pose proof (substitute_type _ _ _ _ _ HW2Q HNat) as HII.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HW2Q)) as HNE.
  pose proof (wf_exp_sub _ _ _ _ _ HQQ Hs) as HSS'.
  pose proof (convert_expression _ _ _ _ _ HSS' HII
    (wf_exp_eq_trans _ _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HQQ) HNE)) as Hsc.
  pose proof (convert_equality _ _ _ _ _ _
    (wf_exp_eq_trans _ _ _ _ _ (wf_exp_eq_succ_sub _ _ _ _ HQQ (natural_second_variable _ _ _ HA))
      (wf_exp_eq_succ_cong _ _ _ Hvar)) HII HNE) as Hsce.
  destruct (typed_lift_instantiation _ _ _ _ _ _ _ _ HW2' HS HNat Hst') as (_ & HTi).
  eapply wf_exp_eq_trans;
    [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HQQ HSS HA) |].
  eapply wf_exp_eq_trans; [|exact (type_substitution_compose _ _ _ _ _ _ _ HST HQ HA)].
  eapply wf_exp_eq_trans.
  - eapply substitute_type_equality;
      [exact (wf_sub_compose _ _ _ _ _ HQQ HSS)
      | exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ HW2 HNat Hst HQQ) | now apply reflexive_expression].
  - eapply wf_exp_eq_trans.
    + exact (type_extension_congruence _ _ _ _ _ _ _ _ _ _ HW2Q HNat HA Hdbl Hsc Hsce).
    + eapply substitute_type_equality;
        [exact (wf_sub_extend _ _ _ _ _ _ HW2S HNat Hst') | exact (wf_sub_eq_sym _ _ _ _ HTi) | now apply reflexive_expression].
Qed.

Lemma native_natural_branches : forall Γ Θ σ i A Z Suc,
    wf_sub Θ Γ σ ->
    wf_exp (a_nat :: Γ) (a_typ i) A ->
    wf_exp Γ (a_sub A (a_extend a_id a_zero)) Z ->
    wf_exp (A :: a_nat :: Γ) (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc ->
    let A' := a_sub A (Syntax.q σ) in
    wf_exp (a_nat :: Θ) (a_typ i) A' /\
    wf_exp Θ (a_sub A' (a_extend a_id a_zero)) (a_sub Z σ) /\
    wf_exp (A' :: a_nat :: Θ) (a_sub A' (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1))))
      (a_sub Suc (Syntax.q (Syntax.q σ))).
Proof.
  intros Γ Θ σ i A Z Suc HS HA HZ HSu; cbn zeta.
  destruct (natural_step_lift_data _ _ _ _ _ HS HA) as (HA' & HQQ & _).
  destruct (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  pose proof (natural_zero_branch_type _ _ _ _ _ HS HA) as HZE.
  pose proof (weaken_zero_substitution _ _ _ _ _ HS HA) as HZE'.
  pose proof (weaken_step_substitution _ _ _ _ _ HS HA) as HSE.
  split; [exact HA' |]. split.
  - eapply convert_expression; [exact (wf_exp_sub _ _ _ _ _ HS HZ) | |].
    + exact (substitute_type _ _ _ _ _ (instantiate_type _ _ _ _
        (wf_nat _ HΘ) (wf_zero _ HΘ)) HA').
    + exact (wf_exp_eq_trans _ _ _ _ _ HZE (wf_exp_eq_sym _ _ _ _ HZE')).
  - eapply convert_expression; [exact (wf_exp_sub _ _ _ _ _ HQQ HSu) | |exact HSE].
    exact (substitute_type _ _ _ _ _ (natural_step_index_substitution _ _ _ HA') HA').
Qed.

Lemma natural_lift_branch_expression : forall Γ Θ i A Suc σ X Y,
    wf_sub Θ Γ σ ->
    wf_exp (a_nat :: Γ) (a_typ i) A ->
    wf_exp (A :: a_nat :: Γ)
      (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc ->
    wf_exp Θ a_nat X -> wf_exp Θ (a_sub A (a_extend σ X)) Y ->
    wf_exp_eq Θ (a_sub A (a_extend σ (a_succ X)))
      (a_sub (a_sub Suc (Syntax.q (Syntax.q σ))) (a_extend (a_extend a_id X) Y))
      (a_sub Suc (a_extend (a_extend σ X) Y)).
Proof.
  intros Γ Θ i A Suc σ X Y HS HA HSu HX HY.
  destruct (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  destruct (natural_step_lift_data _ _ _ _ _ HS HA) as (HA' & HQQ & _).
  destruct (lift_substitution_natural_data _ _ _ HS) as (HQ & _).
  pose proof (wf_nat _ HΓ) as HNat.
  pose proof (wf_nat _ HΘ) as HNat'.
  pose proof (wf_sub_id _ HΘ) as Hid.
  pose proof (wf_sub_compose _ _ _ _ _ Hid HS) as Hσi.
  pose proof (substitute_type _ _ _ _ _ Hσi HNat) as HNsi.
  pose proof (convert_expression _ _ _ _ _ HX HNsi (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ Hσi))) as HXs.
  destruct (typed_lift_instantiation _ _ _ _ _ _ _ _ Hid HS HNat HXs) as (_ & Hqe).
  pose proof (instantiate_type _ _ _ _ HNat' HX) as HI.
  pose proof (wf_sub_compose _ _ _ _ _ HI HQ) as HQI.
  pose proof (wf_sub_extend _ _ _ _ _ _ Hσi HNat HXs) as HSI.
  pose proof (wf_sub_eq_id_compose_left _ _ _ HS) as Hie.
  assert (Hsub : wf_sub_eq Θ (a_nat :: Γ)
     (a_compose (Syntax.q σ) (a_extend a_id X)) (a_extend σ X)).
  {
    eapply wf_sub_eq_trans; [exact Hqe |].
    eapply wf_sub_eq_extend_cong; [exact Hie | exact HNat | now apply reflexive_expression].
  }
  pose proof (substitute_type _ _ _ _ _ HQI HA) as HAI.
  pose proof (substitute_type_equality _ _ _ _ _ _ _ HQI Hsub (reflexive_expression _ _ _ HA)) as HAE.
  pose proof (convert_expression _ _ _ _ _ HY HAI (wf_exp_eq_sym _ _ _ _ HAE)) as HYI.
  destruct (typed_lift_instantiation _ _ _ _ _ _ _ _ HI HQ HA HYI) as (HII & HQqe).
  assert (HExt : wf_sub_eq Θ (A :: a_nat :: Γ)
      (a_compose (Syntax.q (Syntax.q σ)) (a_extend (a_extend a_id X) Y)) (a_extend (a_extend σ X) Y)).
  {
    eapply wf_sub_eq_trans; [exact HQqe |].
    eapply wf_sub_eq_extend_cong; [exact Hsub | exact HA | now apply reflexive_expression].
  }
  destruct (natural_step_branch_type _ _ _ _ _ _ _ HS HA HX HY) as (HT & HTE).
  pose proof (wf_sub_compose _ _ _ _ _ HII HQQ) as Hcomp.
  pose proof (substitute_type _ _ _ _ _ HS HNat) as HNt.
  pose proof (convert_expression _ _ _ _ _ (wf_succ _ _ HX) HNt
     (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS))) as Hsucc.
  pose proof (substitute_type _ _ _ _ _ (wf_sub_extend _ _ _ _ _ _ HS HNat Hsucc) HA) as HTy.
  eapply convert_equality; [|exact HTy|].
  - eapply wf_exp_eq_trans.
    + apply wf_exp_eq_sym; exact (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HII HQQ HSu).
    + exact (wf_exp_eq_sub_cong _ _ _ _ _ _ _ (reflexive_expression _ _ _ HSu) HExt).
  - eapply wf_exp_eq_trans; [|exact HTE].
    exact (substitute_type_equality _ _ _ _ _ _ _ Hcomp HExt (reflexive_expression _ _ _ HT)).
Qed.

Definition natural_recursion_realizes k (Γ Θ : ctx) (i : nat) A Z Suc σ ρ X x :=
  exists b y, eval_exp A (extend_env ρ x) b /\ eval_natrec A Z Suc x ρ y /\
    glued_term (gluing_universes k) Θ (a_sub A (a_extend σ X))
      (a_natrec (a_sub A (Syntax.q σ)) (a_sub Z σ) (a_sub Suc (Syntax.q (Syntax.q σ))) X) b y.

Lemma related_neutral_under_weakening : forall Θ A X n n',
    ne_related n n' -> neutral_under_weakening Θ A X n -> neutral_under_weakening Θ A X n'.
Proof.
  intros Θ A X n n' Hrel HQ Ξ τ Hτ.
  destruct (HQ _ _ Hτ) as (W & HW & HE).
  destruct (Hrel (length Ξ)) as (V & HV & HV').
  pose proof (proj1 (proj2 readback_unique) _ _ _ HW _ HV) as E; subst V.
  exists W; tauto.
Qed.

Lemma natural_recursion_gluing_induction : forall k Γ Θ i A Z Suc σ ρ,
    glued_environment (gluing_universes k) Θ Γ σ ρ ->
    wf_exp (a_nat :: Γ) (a_typ i) A ->
    wf_exp Γ (a_sub A (a_extend a_id a_zero)) Z ->
    wf_exp (A :: a_nat :: Γ) (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc ->
    typing_respects_gluing (gluing_universes k) Γ (a_sub A (a_extend a_id a_zero)) Z ->
    typing_respects_gluing (gluing_universes k) (A :: a_nat :: Γ)
      (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc ->
    (forall X e n, wf_exp Θ a_nat X -> neutral_under_weakening Θ a_nat X n ->
      natural_recursion_realizes k Γ Θ i A Z Suc σ ρ X (d_neut e n)) ->
    forall X r, natural_realizes Θ X r -> forall x, nat_rel r x ->
      natural_recursion_realizes k Γ Θ i A Z Suc σ ρ X x.
Proof.
  intros k Γ Θ i A Z Suc σ ρ HE HA HZ HSu HZg HSg Hne X r HR.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as Hσ.
  destruct (substitution_contexts _ _ _ Hσ) as (HΘ & HΓ).
  pose proof (wf_nat _ HΓ) as HNat.
  pose proof (wf_nat _ HΘ) as HNat'.
  pose proof (substitute_type _ _ _ _ _ Hσ HNat) as HNσ.
  pose proof (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ Hσ)) as HNσe.
  destruct (native_natural_branches _ _ _ _ _ _ _ Hσ HA HZ HSu) as (HA' & HZ' & HS').
  assert (Hinst : forall X, wf_exp Θ a_nat X -> wf_exp Θ (a_typ i) (a_sub A (a_extend σ X))).
  {
    intros P HX. eapply substitute_type; [|exact HA].
    exact (wf_sub_extend _ _ _ _ _ _ Hσ HNat (convert_expression _ _ _ _ _ HX HNσ HNσe)).
  }
  induction HR as [Hc | X r HR IH | X n HX Hn | X Y r HX HXY HR IH]; intros x Hx.
  - inversion Hx; subst.
    destruct (natural_glued_zero_branch _ _ _ _ _ _ _ _ HE HA HZg) as (b & z & Hb & Hz & GZ).
    pose proof (wf_zero _ HΘ) as HX.
    pose proof (wf_natrec _ _ _ _ _ _ HA' HZ' HS' HX) as Hrec.
    pose proof (natural_lift_instance_type _ _ _ _ _ _ Hσ HA HX) as HAE.
    exists b, z; split; [exact Hb |]. split; [now apply eval_natrec_zero |].
    eapply glued_term_expression_change;
      [exact HU | exact HC | exact GZ | exact (convert_expression _ _ _ _ _ Hrec (Hinst _ HX) HAE) |].
    apply wf_exp_eq_sym.
    exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_nat_beta_zero _ _ _ _ _ HA' HZ' HS') (Hinst _ HX) HAE).
  - inversion Hx; subst.
    destruct (IH _ H0) as (b & y & Hb & Hy & GY).
    pose proof (natural_glued_term (gluing_universes k) _ _ _ _ HR H0) as GX.
    destruct (natural_glued_successor_branch _ _ _ _ _ _ _ _ _ _ _ _ _ HE HA HSg GX Hb GY)
      as (c & z & Hc & Hz & GZ).
    pose proof (natural_realizes_typing _ _ _ HR) as HX.
    pose proof (glued_term_typing _ _ _ _ _ _ GY) as HY.
    pose proof (wf_succ _ _ HX) as HXs.
    pose proof (wf_natrec _ _ _ _ _ _ HA' HZ' HS' HXs) as Hrec.
    pose proof (natural_lift_instance_type _ _ _ _ _ _ Hσ HA HXs) as HAE.
    pose proof (wf_exp_eq_nat_beta_succ _ _ _ _ _ _ HA' HZ' HS' HX) as Hβ.
    pose proof (natural_lift_branch_expression _ _ _ _ _ _ _ _ Hσ HA HSu HX HY) as HSE.
    exists c, z; split; [exact Hc |]. split; [eapply eval_natrec_succ; eassumption |].
    eapply glued_term_expression_change;
      [exact HU | exact HC | exact GZ | exact (convert_expression _ _ _ _ _ Hrec (Hinst _ HXs) HAE) |].
    apply wf_exp_eq_sym.
    eapply wf_exp_eq_trans;
      [exact (convert_equality _ _ _ _ _ _ Hβ (Hinst _ HXs) HAE) | exact HSE].
  - inversion Hx; subst.
    eapply Hne; [exact HX |].
    eapply related_neutral_under_weakening; eassumption.
  - destruct (IH _ Hx) as (b & y & Hb & Hy & GY).
    pose proof (natural_realizes_typing _ _ _ HR) as HY.
    pose proof (natural_lift_instance_type _ _ _ _ _ _ Hσ HA HX) as HAE.
    pose proof (natural_lift_instance_type _ _ _ _ _ _ Hσ HA HY) as HBE.
    pose proof (convert_expression _ _ _ _ _ HY HNσ HNσe) as HYs.
    pose proof (convert_equality _ _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ HXY) HNσ HNσe) as HXYs.
    pose proof (type_extension_congruence _ _ _ _ _ _ _ _ _ _ Hσ HNat HA
      (reflexive_substitution _ _ _ Hσ) HYs HXYs) as Htype.
    pose proof (wf_natrec _ _ _ _ _ _ HA' HZ' HS' HX) as Hrec.
    exists b, y; split; [exact Hb |]. split; [exact Hy |].
    eapply glued_term_type_change; [|exact (Hinst _ HX)|exact Htype].
    eapply glued_term_expression_change; [exact HU | exact HC | exact GY | |].
    + eapply convert_expression; [exact Hrec | exact (Hinst _ HY) |].
      exact (wf_exp_eq_trans _ _ _ _ _ HAE (wf_exp_eq_sym _ _ _ _ Htype)).
    + eapply convert_equality; [|exact (Hinst _ HY) | exact HBE].
      eapply wf_exp_eq_natrec_cong;
        [exact HA' | now apply reflexive_expression | now apply reflexive_expression
        | now apply reflexive_expression | exact (wf_exp_eq_sym _ _ _ _ HXY)].
Qed.

Definition natural_neutral_respects_gluing :=
  forall k Γ Θ i A Z Suc σ ρ X e n,
    i < k ->
    glued_environment (gluing_universes k) Θ Γ σ ρ ->
    wf_exp (a_nat :: Γ) (a_typ i) A ->
    wf_exp Γ (a_sub A (a_extend a_id a_zero)) Z ->
    wf_exp (A :: a_nat :: Γ) (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc ->
    typing_respects_gluing (gluing_universes k) (a_nat :: Γ) (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) Γ (a_sub A (a_extend a_id a_zero)) Z ->
    typing_respects_gluing (gluing_universes k) (A :: a_nat :: Γ)
      (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc ->
    wf_exp Θ a_nat X -> neutral_under_weakening Θ a_nat X n ->
    natural_recursion_realizes k Γ Θ i A Z Suc σ ρ X (d_neut e n).

Lemma natural_eliminator_from_neutrals :
    natural_neutral_respects_gluing -> natural_eliminator_respects_gluing.
Proof.
  intros Hne k Γ i A Z Suc M Hk0 Hki HA HZ HSuc HM HAg HZg HSg HMg Θ σ ρ HE.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  destruct (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  pose proof (wf_nat _ HΓ) as HN.
  destruct (HMg _ _ _ HE) as (a & m & Ha & Hm & GM).
  inversion Ha; subst a.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GM (wf_nat _ HΘ)
    (wf_exp_eq_nat_sub _ _ _ HS)) as GM'.
  destruct (glued_term_as_natural _ _ _ _ HU HC GM') as (r & Hr & Hrel).
  destruct (natural_recursion_gluing_induction _ _ _ _ _ _ _ _ _ HE HA HZ HSuc HZg HSg
    (fun X e n => Hne _ _ _ _ _ _ _ _ _ X e n Hki HE HA HZ HSuc HAg HZg HSg)
    _ _ Hr _ Hrel) as (b & y & Hb & Hy & GY).
  pose proof (substitute_type _ _ _ _ _ (instantiate_type _ _ _ _ HN HM) HA) as HRT.
  pose proof (substitute_type _ _ _ _ _ HS HRT) as HRs.
  pose proof (substitute_instantiated_type _ _ _ _ _ _ _ _ HS HN HA HM) as HRE.
  pose proof (wf_exp_sub _ _ _ _ _ HS (wf_natrec _ _ _ _ _ _ HA HZ HSuc HM)) as HRw.
  pose proof (wf_exp_eq_natrec_sub _ _ _ _ _ _ _ _ HS HA HZ HSuc HM) as HSE.
  exists b, y; split.
  - eapply eval_exp_sub; [eapply eval_sub_extend; [apply eval_sub_id | exact Hm] | exact Hb].
  - split; [eapply eval_exp_natrec; eassumption |].
    eapply glued_term_expression_change.
    + exact HU.
    + exact HC.
    + exact (glued_term_type_change _ _ _ _ _ _ _ _ GY HRs (wf_exp_eq_sym _ _ _ _ HRE)).
    + exact HRw.
    + eapply convert_equality; [apply wf_exp_eq_sym; exact HSE | exact HRs | apply wf_exp_eq_sym; exact HRE].
Qed.

Lemma lift_substitution_composition_as : forall Γ Δ Θ σ τ i A D E,
    wf_sub Δ Γ σ -> wf_sub Θ Δ τ ->
    wf_exp Γ (a_typ i) A -> wf_exp Δ (a_typ i) D -> wf_exp Θ (a_typ i) E ->
    wf_exp_eq Δ (a_typ i) D (a_sub A σ) -> wf_exp_eq Θ (a_typ i) E (a_sub D τ) ->
    wf_sub_eq (E :: Θ) (A :: Γ) (a_compose (Syntax.q σ) (Syntax.q τ)) (Syntax.q (a_compose σ τ)).
Proof.
  intros Γ Δ Θ σ τ i A D E HS HT HA HD HE HDA HED.
  destruct (lift_substitution_as_data _ _ _ _ _ _ HS HA HD HDA) as (HSW & Hx & Hq & HP).
  destruct (lift_substitution_as_data _ _ _ _ _ _ HT HD HE HED) as (HTW & Hy & Hq' & HP').
  pose proof (wf_sub_weaken _ _ (proj1 (substitution_contexts _ _ _ Hq))) as HW.
  pose proof (wf_sub_weaken _ _ (proj1 (substitution_contexts _ _ _ Hq'))) as HW'.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HC.
  pose proof (wf_sub_compose _ _ _ _ _ HW' HC) as HCW.
  pose proof (wf_sub_compose _ _ _ _ _ Hq' HSW) as HSWQ.
  pose proof (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HS HT HW') as Hassoc.
  assert (Htail : wf_sub_eq (E :: Θ) Γ
    (a_compose (a_compose σ a_weaken) (Syntax.q τ)) (a_compose (a_compose σ τ) a_weaken)).
  {
    eapply wf_sub_eq_trans; [exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HS HW Hq') |].
    eapply wf_sub_eq_trans; [exact (wf_sub_eq_compose_cong _ _ _ _ _ _ _ HP' (reflexive_substitution _ _ _ HS)) |].
    apply wf_sub_eq_sym; exact Hassoc.
  }
  assert (Hty : wf_exp_eq (E :: Θ) (a_typ i) (a_sub D (a_compose τ a_weaken))
      (a_sub A (a_compose (a_compose σ a_weaken) (Syntax.q τ)))).
  {
    eapply wf_exp_eq_trans.
    - eapply substitute_type_equality; [exact HTW | now apply reflexive_substitution | exact HDA].
    - eapply wf_exp_eq_trans.
      + apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HTW HS HA).
      + apply wf_exp_eq_sym; eapply substitute_type_equality; [exact HSWQ | | now apply reflexive_expression].
        exact (wf_sub_eq_trans _ _ _ _ _ Htail Hassoc).
  }
  eapply wf_sub_eq_trans; [exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ HSW HA Hx Hq') |].
  eapply wf_sub_eq_extend_cong; [exact Htail | exact HA |].
  exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_var_0_sub _ _ _ _ _ _ HTW HD Hy)
    (substitute_type _ _ _ _ _ HSWQ HA) Hty).
Qed.

Lemma quote_native_natural_recursion : forall k Γ Θ i A Z Suc σ ρ X n z,
    i < k ->
    glued_environment (gluing_universes k) Θ Γ σ ρ ->
    wf_exp (a_nat :: Γ) (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) (a_nat :: Γ) (a_typ i) A ->
    typing_respects_gluing (gluing_universes k) Γ (a_sub A (a_extend a_id a_zero)) Z ->
    typing_respects_gluing (gluing_universes k) (A :: a_nat :: Γ)
      (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc ->
    eval_exp Z ρ z -> quoted_neutral Θ a_nat X n ->
    quoted_neutral Θ (a_sub (a_sub A (Syntax.q σ)) (a_extend a_id X))
      (a_natrec (a_sub A (Syntax.q σ)) (a_sub Z σ) (a_sub Suc (Syntax.q (Syntax.q σ))) X)
      (d_natrec ρ A z Suc n).
Proof.
  intros k Γ Θ i A Z Suc σ ρ X n z Hk HE HA HAg HZg HSg Hz HX.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (gluing_universes_weaken k) as HW.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  destruct (substitution_contexts _ _ _ HS) as (HΘ & HΓ).
  pose proof (lift_glued_environment_natural _ _ _ _ _ HE) as HE'.
  destruct (extract_glued_code _ _ _ _ _ _ _ Hk HE' HAg) as (b & R & Hb & GA).
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HA'.
  pose proof (expression_context _ _ _ HA') as HΘN.
  pose proof (quotation_of_type _ _ _ _ (proj1 (quoted_candidate_reflects _ _ _ _ _ _ HU GA))
    _ _ (weakening_identity _ HΘN)) as HQA.
  pose proof (quote_type_conversion _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ (type_substitution_identity _ _ _ HA')) HQA) as HAq.
  pose proof (lift_glued_environment _ _ _ _ _ _ _ _ _ HU HC HW HE' HA Hb GA) as HE''.
  destruct (HSg _ _ _ HE'') as (bs & r & Hbs & Hr & GS).
  destruct (natural_glued_zero_branch _ _ _ _ _ _ _ _ HE HA HZg) as (b0 & z' & Hb0 & Hz' & GZ).
  pose proof (exp_unique _ _ _ Hz' _ Hz) as E; subst z'.
  pose proof (substitute_type _ _ _ _ _ (instantiate_type _ _ _ _ (wf_nat _ HΘ) (wf_zero _ HΘ)) HA') as HZT.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GZ HZT
     (wf_exp_eq_sym _ _ _ _ (weaken_zero_substitution _ _ _ _ _ HS HA))) as GZ'.
  pose proof (substitute_type _ _ _ _ _ (natural_step_index_substitution _ _ _ HA') HA') as HST.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GS HST (weaken_step_substitution _ _ _ _ _ HS HA)) as GS'.
  set (x := d_neut d_nat (d_var (length Θ))).
  assert (Hbs' : eval_exp A (extend_env ρ (d_succ x)) bs).
  {
    inversion Hbs; subst.
    assert (Hstep : eval_sub (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))
        (extend_env (extend_env ρ x) (d_neut b (d_var (S (length Θ)))))
        (extend_env ρ (d_succ x))).
    { eapply eval_sub_extend.
      - eapply eval_sub_compose; apply eval_sub_weaken.
      - apply eval_exp_succ, eval_exp_var. }
    resolve_eval. assumption.
  }
  eapply quote_neutral_natrec; [exact HA' | exact Hb | exact HAq | exact Hb0
    | exact (glued_term_quote _ _ _ _ _ _ GZ') | exact Hbs' | exact Hr
    | exact (glued_term_quote _ _ _ _ _ _ GS') | exact HX].
Qed.

Lemma natural_recursor_weaken_syntax : forall Γ Θ Ξ σ τ i A Z Suc X,
    wf_sub Θ Γ σ -> wf_sub Ξ Θ τ ->
    wf_exp (a_nat :: Γ) (a_typ i) A ->
    wf_exp Γ (a_sub A (a_extend a_id a_zero)) Z ->
    wf_exp (A :: a_nat :: Γ) (a_sub A (a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)))) Suc ->
    wf_exp Θ a_nat X ->
    let R s Y := a_natrec (a_sub A (Syntax.q s)) (a_sub Z s) (a_sub Suc (Syntax.q (Syntax.q s))) Y in
    let B := a_sub (a_sub A (Syntax.q (a_compose σ τ))) (a_extend a_id (a_sub X τ)) in
    wf_exp Ξ (a_typ i) B /\
    wf_exp_eq Ξ (a_typ i) (a_sub (a_sub A (a_extend σ X)) τ) B /\
    wf_exp_eq Ξ B (a_sub (R σ X) τ) (R (a_compose σ τ) (a_sub X τ)).
Proof.
  intros Γ Θ Ξ σ τ i A Z Suc X HS HT HA HZ HSu HX; cbn zeta.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HC.
  pose proof (wf_nat _ (proj2 (substitution_contexts _ _ _ HS))) as HNG.
  pose proof (wf_nat _ (proj1 (substitution_contexts _ _ _ HS))) as HNT.
  pose proof (wf_nat _ (proj1 (substitution_contexts _ _ _ HT))) as HNX.
  destruct (native_natural_branches _ _ _ _ _ _ _ HS HA HZ HSu) as (HA' & HZ' & HSu').
  destruct (native_natural_branches _ _ _ _ _ _ _ HT HA' HZ' HSu') as (HA'' & HZ'' & HSu'').
  destruct (native_natural_branches _ _ _ _ _ _ _ HC HA HZ HSu) as (HAC & HZC & HSuC).
  destruct (lift_substitution_natural_data _ _ _ HS) as (HQ & _).
  destruct (lift_substitution_natural_data _ _ _ HT) as (HQT & _).
  pose proof (wf_sub_compose _ _ _ _ _ HQT HQ) as HQQ.
  pose proof (lift_substitution_composition_as _ _ _ _ _ _ _ _ _ HS HT HNG HNT HNX
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HS))
    (wf_exp_eq_sym _ _ _ _ (wf_exp_eq_nat_sub _ _ _ HT))) as HQE.
  assert (HAE : wf_exp_eq (a_nat :: Ξ) (a_typ i) (a_sub (a_sub A (Syntax.q σ)) (Syntax.q τ))
      (a_sub A (Syntax.q (a_compose σ τ)))).
  {
    eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HQT HQ HA) |].
    eapply substitute_type_equality; [exact HQQ | exact HQE | now apply reflexive_expression].
  }
  pose proof (convert_expression _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HT HX) HNX) as HXt0.
  pose proof (HXt0 (wf_exp_eq_nat_sub _ _ _ HT)) as HXt.
  pose proof (instantiate_type _ _ _ _ HNX HXt) as HIX.
  pose proof (substitute_type _ _ _ _ _ HIX HAC) as HBT.
  pose proof (substitute_type_equality _ _ _ _ _ _ _ HIX (reflexive_substitution _ _ _ HIX) HAE) as HIXE.
  pose proof (natural_lift_instance_type _ _ _ _ _ _ HT HA' HXt) as HL.
  pose proof (natural_lift_instance_type _ _ _ _ _ _ HC HA HXt) as HCL.
  pose proof (substitute_instantiated_type _ _ _ _ _ _ _ _ HT HNT HA' HX) as HIE.
  assert (HrawE : wf_exp_eq Ξ (a_typ i) (a_sub (a_sub A (a_extend σ X)) τ)
        (a_sub (a_sub A (Syntax.q (a_compose σ τ))) (a_extend a_id (a_sub X τ)))).
  {
    eapply wf_exp_eq_trans.
    - eapply substitute_type_equality; [exact HT | now apply reflexive_substitution |].
      apply wf_exp_eq_sym; exact (natural_lift_instance_type _ _ _ _ _ _ HS HA HX).
    - eapply wf_exp_eq_trans; [exact HIE |].
      eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact HL | exact HIXE].
  }
  split; [exact HBT |]. split; [exact HrawE |].
  pose proof (wf_exp_eq_natrec_sub _ _ _ _ _ _ _ _ HT HA' HZ' HSu' HX) as HRE.
  eapply wf_exp_eq_trans.
  - exact (convert_equality _ _ _ _ _ _ HRE HBT
      (wf_exp_eq_trans _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ HL) HIXE)).
  - eapply convert_equality; [|exact HBT | exact HIXE].
    eapply wf_exp_eq_natrec_cong; [exact HA'' | exact HAE | | | now apply reflexive_expression].
    + eapply convert_equality; [apply wf_exp_eq_sym; exact (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HT HS HZ)
      | exact (substitute_type _ _ _ _ _ (instantiate_type _ _ _ _ HNX (wf_zero _ (expression_context _ _ _ HNX))) HA'') |].
      eapply wf_exp_eq_trans.
      * exact (natural_zero_branch_type _ _ _ _ _ HC HA).
      * eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact (weaken_zero_substitution _ _ _ _ _ HC HA) |].
        apply wf_exp_eq_sym.
        pose proof (instantiate_type _ _ _ _ HNX (wf_zero _ (expression_context _ _ _ HNX))) as HIZ.
        exact (substitute_type_equality _ _ _ _ _ _ _ HIZ (reflexive_substitution _ _ _ HIZ) HAE).
    + destruct (natural_step_lift_data _ _ _ _ _ HS HA) as (_ & HQQS & _).
      destruct (natural_step_lift_data _ _ _ _ _ HT HA') as (_ & HQQT & _).
      pose proof (lift_substitution_composition_as _ _ _ _ _ _ _ _ _ HQ HQT HA HA' HA''
        (reflexive_expression _ _ _ HA') (reflexive_expression _ _ _ HA'')) as HSS.
      destruct (lift_substitution_as_data _ _ _ _ _ _ HQQ HA HA''
        (wf_exp_eq_sym _ _ _ _ (type_substitution_compose _ _ _ _ _ _ _ HQT HQ HA))) as (_ & Hfresh & Hlift & _).
      assert (HSSE : wf_sub_eq (a_sub (a_sub A (Syntax.q σ)) (Syntax.q τ) :: a_nat :: Ξ)
        (A :: a_nat :: Γ) (Syntax.q (a_compose (Syntax.q σ) (Syntax.q τ))) (Syntax.q (Syntax.q (a_compose σ τ)))).
      {
        eapply wf_sub_eq_extend_cong.
        - eapply wf_sub_eq_compose_cong; [|exact HQE].
          apply reflexive_substitution, wf_sub_weaken.
          exact (proj1 (substitution_contexts _ _ _ Hlift)).
        - exact HA.
        - now apply reflexive_expression.
      }
      pose proof (wf_sub_eq_trans _ _ _ _ _ HSS HSSE) as HSQ.
      eapply convert_equality.
      * eapply wf_exp_eq_trans.
        -- apply wf_exp_eq_sym; exact (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HQQT HQQS HSu).
        -- exact (wf_exp_eq_sub_cong _ _ _ _ _ _ _ (reflexive_expression _ _ _ HSu) HSQ).
      * exact (substitute_type _ _ _ _ _ (natural_step_index_substitution _ _ _ HA'') HA'').
      * eapply wf_exp_eq_trans.
        -- exact (type_substitution_compose _ _ _ _ _ _ _ HQQT HQQS
             (substitute_type _ _ _ _ _ (natural_step_index_substitution _ _ _ HA) HA)).
        -- eapply wf_exp_eq_trans.
           ++ eapply substitute_type_equality; [exact HQQT | now apply reflexive_substitution |].
              exact (weaken_step_substitution _ _ _ _ _ HS HA).
           ++ exact (weaken_step_substitution _ _ _ _ _ HT HA').
Qed.

Lemma gluing_natural_neutral : natural_neutral_respects_gluing.
Proof.
  intros k Γ Θ i A Z Suc σ ρ X e n Hk HE HA HZ HSu HAg HZg HSg HX Hne.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (gluing_universes_weaken k) as HW.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (natural_glued_term (gluing_universes k) Θ X (d_neut d_nat n) (d_neut e n)
    (realizes_neutral _ _ _ HX Hne) (nat_rel_neut _ _ _ _ (typed_neutral_self _ _ _ _ HX Hne))) as GX.
  destruct (natural_glued_motive _ _ _ _ _ _ _ _ _ Hk HE HAg GX) as (b & R & Hb & GB).
  destruct (natural_glued_zero_branch _ _ _ _ _ _ _ _ HE HA HZg) as (bzero & z & Hzero & Hz & GZ).
  exists b, (d_neut b (d_natrec ρ A z Suc n)); split; [exact Hb |]. split.
  - eapply eval_natrec_neut; eassumption.
  - destruct (native_natural_branches _ _ _ _ _ _ _ HS HA HZ HSu) as (HA' & HZ' & HSu').
    pose proof (glued_type_well_formed _ _ _ _ _ _ GB) as HBT.
    pose proof (natural_lift_instance_type _ _ _ _ _ _ HS HA HX) as HAE.
    eapply reflect_glued_term; [exact HU | exact GB | |].
    + exact (convert_expression _ _ _ _ _ (wf_natrec _ _ _ _ _ _ HA' HZ' HSu' HX) HBT HAE).
    + intros Ξ τ Hτ.
      pose proof (weakening_is_typed _ _ _ Hτ) as HT.
      pose proof (glued_environment_weaken _ _ _ _ _ HU HC HW HE _ _ Hτ) as HE'.
      pose proof (wf_nat _ (proj1 (substitution_contexts _ _ _ HT))) as HN.
      pose proof (quote_neutral_type_conversion _ _ _ _ _ _ HN (wf_exp_eq_nat_sub _ _ _ HT)
        (Hne _ _ Hτ)) as HNX.
      pose proof (quote_native_natural_recursion _ _ _ _ _ _ _ _ _ _ _ _ Hk HE' HA HAg HZg HSg Hz HNX) as HQR.
      destruct (natural_recursor_weaken_syntax _ _ _ _ _ _ _ _ _ _ HS HT HA HZ HSu HX) as (HFT & HFe & HRe).
      eapply quote_neutral_type_conversion; [exact (substitute_type _ _ _ _ _ HT HBT) | exact (wf_exp_eq_sym _ _ _ _ HFe) |].
      eapply quote_neutral_conversion; [exact HRe | exact HQR].
Qed.

Lemma gluing_natural_eliminator : natural_eliminator_respects_gluing.
Proof. exact (natural_eliminator_from_neutrals gluing_natural_neutral). Qed.

Lemma equality_instantiation_at : forall Γ Θ i A σ X Y,
    wf_sub Θ Γ σ -> wf_exp Γ (a_typ i) A ->
    wf_exp Θ (a_sub A σ) X -> wf_exp Θ (a_sub A σ) Y ->
    let E := a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0) in
    wf_exp (A :: Γ) (a_typ i) (a_sub A a_weaken) /\
    wf_exp (a_sub A a_weaken :: A :: Γ) (a_typ i) E /\
    wf_exp_eq Θ (a_typ i) (a_sub (a_sub A a_weaken) (a_extend σ X)) (a_sub A σ) /\
    wf_exp_eq Θ (a_typ i) (a_sub E (a_extend (a_extend σ X) Y)) (a_eq (a_sub A σ) X Y).
Proof.
  intros Γ Θ i A σ X Y HS HA HX HY; cbn zeta.
  pose proof (expression_context _ _ _ HA) as HG.
  pose proof (wf_ctx_extend _ _ _ HG HA) as HGA.
  pose proof (weaken_type _ _ _ _ HGA HA) as HAW.
  pose proof (wf_ctx_extend _ _ _ HGA HAW) as HGAA.
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HX) as HSX.
  pose proof (substitute_type _ _ _ _ _ HSX HAW) as HAWX.
  pose proof (substitute_weakening _ _ _ _ _ _ _ _ HS HA HA HX) as HWX.
  pose proof (convert_expression _ _ _ _ _ HY HAWX (wf_exp_eq_sym _ _ _ _ HWX)) as HYw.
  pose proof (wf_sub_extend _ _ _ _ _ _ HSX HAW HYw) as HSXY.
  pose proof (wf_sub_weaken _ _ HGA) as HW.
  pose proof (wf_sub_weaken _ _ HGAA) as HWW.
  pose proof (wf_sub_compose _ _ _ _ _ HWW HW) as HW2.
  pose proof (substitute_type _ _ _ _ _ HW2 HA) as HA2.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_compose _ _ _ _ _ _ _ HWW HW HA)) as HA2e.
  pose proof (convert_expression _ _ _ _ _ (wf_vlookup _ _ _ HGAA (there _ _ _ _ (here A Γ))) HA2 HA2e) as H1.
  pose proof (convert_expression _ _ _ _ _ (type_of_first_variable _ _ HGAA) HA2 HA2e) as H0.
  pose proof (wf_eq _ _ _ _ _ HA2 H1 H0) as Hq.
  split; [exact HAW |]. split; [exact Hq |]. split; [exact HWX |].
  pose proof (substitute_two_weakenings _ _ _ _ _ _ _ _ _ HS HA HA HX HYw) as HAe.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  assert (HXe : wf_exp_eq Θ (a_sub A σ) (a_sub (a_var 1) (a_extend (a_extend σ X) Y)) X).
  {
    eapply wf_exp_eq_trans.
    - exact (convert_equality _ _ _ _ _ _ (wf_exp_eq_var_S_sub _ _ _ _ _ _ _ _ HSX HAW HYw (here A Γ)) HAs HWX).
    - exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ HS HA HX).
  }
  pose proof (convert_equality _ _ _ _ _ _ (wf_exp_eq_var_0_sub _ _ _ _ _ _ HSX HAW HYw) HAs HWX) as HYe.
  pose proof (substitute_type _ _ _ _ _ HSXY HA2) as HA2s.
  eapply wf_exp_eq_trans; [exact (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HSXY HA2 H1 H0) |].
  eapply wf_exp_eq_eq_cong.
  - exact HAe.
  - exact (convert_equality _ _ _ _ _ _ HXe HA2s (wf_exp_eq_sym _ _ _ _ HAe)).
  - exact (convert_equality _ _ _ _ _ _ HYe HA2s (wf_exp_eq_sym _ _ _ _ HAe)).
Qed.

Lemma glued_equality_motive_environment : forall k Γ Θ i A σ ρ a X x Y y P p,
    glued_environment (gluing_universes k) Θ Γ σ ρ ->
    wf_exp Γ (a_typ i) A -> eval_exp A ρ a ->
    glued_term (gluing_universes k) Θ (a_sub A σ) X a x ->
    glued_term (gluing_universes k) Θ (a_sub A σ) Y a y ->
    glued_term (gluing_universes k) Θ (a_eq (a_sub A σ) X Y) P (d_eq a x y) p ->
    glued_environment (gluing_universes k) Θ (equality_context Γ A)
      (a_extend (a_extend (a_extend σ X) Y) P) (extend_three ρ x y p).
Proof.
  intros k Γ Θ i A σ ρ a X x Y y P p HE HA Ha GX GY GP.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (glued_term_typing _ _ _ _ _ _ GX) as HX.
  pose proof (glued_term_typing _ _ _ _ _ _ GY) as HY.
  destruct (equality_instantiation_at _ _ _ _ _ _ _ HS HA HX HY) as (HAW & HEty & HAe & HEe).
  pose proof (glued_environment_extend _ _ _ _ _ _ _ _ _ _ HU HC HE HA Ha GX) as HEX.
  pose proof (glued_environment_typing _ _ _ _ _ HEX) as HSX.
  pose proof (substitute_type _ _ _ _ _ HSX HAW) as HAW'.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GY HAW' (wf_exp_eq_sym _ _ _ _ HAe)) as GY'.
  assert (Haw : eval_exp (a_sub A a_weaken) (extend_env ρ x) a).
  { eapply eval_exp_sub; [apply eval_sub_weaken | exact Ha]. }
  pose proof (glued_environment_extend _ _ _ _ _ _ _ _ _ _ HU HC HEX HAW Haw GY') as HExy.
  pose proof (glued_environment_typing _ _ _ _ _ HExy) as HSxy.
  pose proof (substitute_type _ _ _ _ _ HSxy HEty) as HEty'.
  assert (Hev : eval_exp (a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0))
                 (extend_env (extend_env ρ x) y) (d_eq a x y)).
  {
    eapply eval_exp_eq.
    - eapply eval_exp_sub; [eapply eval_sub_compose; apply eval_sub_weaken | exact Ha].
    - apply eval_exp_var.
    - apply eval_exp_var.
  }
  eapply glued_environment_extend; [exact HU | exact HC | exact HExy | exact HEty | exact Hev |].
  exact (glued_term_type_change _ _ _ _ _ _ _ _ GP HEty' (wf_exp_eq_sym _ _ _ _ HEe)).
Qed.

Lemma equality_lift_second : forall Γ Θ i A σ,
    wf_sub Θ Γ σ -> wf_exp Γ (a_typ i) A ->
    let A' := a_sub A σ in
    let A2 := a_sub A a_weaken in
    let A2' := a_sub A' a_weaken in
    wf_exp Θ (a_typ i) A' /\
    wf_exp (A :: Γ) (a_typ i) A2 /\
    wf_exp (A' :: Θ) (a_typ i) A2' /\
    wf_exp_eq (A' :: Θ) (a_typ i) A2' (a_sub A2 (Syntax.q σ)) /\
    wf_sub (A' :: Θ) (A :: Γ) (Syntax.q σ) /\
    wf_sub (A2' :: A' :: Θ) (A2 :: A :: Γ) (Syntax.q (Syntax.q σ)).
Proof.
  intros Γ Θ i A σ HS HA; cbn zeta.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HA'.
  destruct (lift_substitution_as_data _ _ _ _ _ _ HS HA HA' (reflexive_expression _ _ _ HA')) as (HSW & Hx & HQ & HP).
  pose proof (wf_sub_weaken _ _ (proj2 (substitution_contexts _ _ _ HQ))) as HW.
  pose proof (wf_sub_weaken _ _ (proj1 (substitution_contexts _ _ _ HQ))) as HW'.
  pose proof (substitute_type _ _ _ _ _ HW HA) as HAW.
  pose proof (substitute_type _ _ _ _ _ HW' HA') as HAW'.
  assert (HE : wf_exp_eq (a_sub A σ :: Θ) (a_typ i)
    (a_sub (a_sub A σ) a_weaken) (a_sub (a_sub A a_weaken) (Syntax.q σ))).
  {
    apply wf_exp_eq_sym.
    eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HQ HW HA) |].
    eapply wf_exp_eq_trans; [|exact (type_substitution_compose _ _ _ _ _ _ _ HW' HS HA)].
    eapply substitute_type_equality; [exact (wf_sub_compose _ _ _ _ _ HQ HW) | exact HP | now apply reflexive_expression].
  }
  destruct (lift_substitution_as_data _ _ _ _ _ _ HQ HAW HAW' HE) as (_ & _ & HQQ & _).
  repeat split; assumption.
Qed.

Lemma equality_lift_inf_type : forall Γ i A,
    wf_exp Γ (a_typ i) A ->
    let G := a_sub A a_weaken :: A :: Γ in
    let C := a_sub A (a_compose a_weaken a_weaken) in
    wf_exp G (a_typ i) C /\ wf_exp G C (a_var 1) /\ wf_exp G C (a_var 0).
Proof.
  intros Γ i A HA; cbn zeta.
  pose proof (wf_ctx_extend _ _ _ (expression_context _ _ _ HA) HA) as H1.
  pose proof (weaken_type _ _ _ _ H1 HA) as HAw.
  pose proof (wf_ctx_extend _ _ _ H1 HAw) as H2.
  pose proof (wf_sub_weaken _ _ H1) as HW.
  pose proof (wf_sub_weaken _ _ H2) as HW'.
  pose proof (substitute_type _ _ _ _ _ (wf_sub_compose _ _ _ _ _ HW' HW) HA) as HT.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_compose _ _ _ _ _ _ _ HW' HW HA)) as HE.
  split; [exact HT |]. split.
  - exact (convert_expression _ _ _ _ _ (wf_vlookup _ _ _ H2 (there _ _ _ _ (here A Γ))) HT HE).
  - exact (convert_expression _ _ _ _ _ (type_of_first_variable _ _ H2) HT HE).
Qed.

Lemma equality_lift_third : forall Γ Θ i A σ,
    wf_sub Θ Γ σ -> wf_exp Γ (a_typ i) A ->
    let A' := a_sub A σ in
    let E := a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0) in
    let E' := a_eq (a_sub A' (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0) in
    wf_exp (a_sub A a_weaken :: A :: Γ) (a_typ i) E /\
    wf_exp (a_sub A' a_weaken :: A' :: Θ) (a_typ i) E' /\
    wf_exp_eq (a_sub A' a_weaken :: A' :: Θ) (a_typ i) E' (a_sub E (Syntax.q (Syntax.q σ))) /\
    wf_sub (equality_context Θ A') (equality_context Γ A) (Syntax.q (Syntax.q (Syntax.q σ))).
Proof.
  intros Γ Θ i A σ HS HA; cbn zeta.
  destruct (equality_lift_second _ _ _ _ _ HS HA) as (HA' & HAW & HAW' & HAE & HQ & HQQ).
  destruct (equality_lift_inf_type _ _ _ HA) as (HC & HX & HY).
  destruct (equality_lift_inf_type _ _ _ HA') as (HC' & HX' & HY').
  pose proof (wf_eq _ _ _ _ _ HC HX HY) as HE.
  pose proof (wf_eq _ _ _ _ _ HC' HX' HY') as HE'.
  destruct (lift_substitution_as_data _ _ _ _ _ _ HS HA HA' (reflexive_expression _ _ _ HA')) as (HsW & H0 & _ & HQE).
  destruct (lift_substitution_as_data _ _ _ _ _ _ HQ HAW HAW' HAE) as (HqW & Hq0 & _ & HQQE).
  pose proof (wf_sub_weaken _ _ (proj1 (substitution_contexts _ _ _ HQ))) as HWt.
  pose proof (wf_sub_weaken _ _ (proj2 (substitution_contexts _ _ _ HQ))) as HWs.
  pose proof (wf_sub_weaken _ _ (proj1 (substitution_contexts _ _ _ HQQ))) as HWt'.
  pose proof (wf_sub_weaken _ _ (proj2 (substitution_contexts _ _ _ HQQ))) as HWs'.
  pose proof (wf_sub_compose _ _ _ _ _ HWs' HWs) as HW2.
  pose proof (wf_sub_compose _ _ _ _ _ HWt' HWt) as HW2'.
  assert (Hdbl : wf_sub_eq (a_sub (a_sub A σ) a_weaken :: a_sub A σ :: Θ) Γ
    (a_compose (a_compose a_weaken a_weaken) (Syntax.q (Syntax.q σ)))
    (a_compose σ (a_compose a_weaken a_weaken))).
  {
    eapply wf_sub_eq_trans; [exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HWs HWs' HQQ) |].
    eapply wf_sub_eq_trans;
      [exact (wf_sub_eq_compose_cong _ _ _ _ _ _ _ HQQE (reflexive_substitution _ _ _ HWs)) |].
    eapply wf_sub_eq_trans.
    - apply wf_sub_eq_sym; exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HWs HQ HWt').
    - eapply wf_sub_eq_trans;
        [exact (wf_sub_eq_compose_cong _ _ _ _ _ _ _ (reflexive_substitution _ _ _ HWt') HQE) |].
      exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HS HWt HWt').
  }
  assert (Hcarry : wf_exp_eq (a_sub (a_sub A σ) a_weaken :: a_sub A σ :: Θ) (a_typ i)
    (a_sub (a_sub A (a_compose a_weaken a_weaken)) (Syntax.q (Syntax.q σ)))
    (a_sub (a_sub A σ) (a_compose a_weaken a_weaken))).
  {
    eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HQQ HW2 HA) |].
    eapply wf_exp_eq_trans; [|exact (type_substitution_compose _ _ _ _ _ _ _ HW2' HS HA)].
    eapply substitute_type_equality; [exact (wf_sub_compose _ _ _ _ _ HQQ HW2) | exact Hdbl | now apply reflexive_expression].
  }
  assert (Hcoerce : wf_exp_eq (a_sub (a_sub A σ) a_weaken :: a_sub A σ :: Θ) (a_typ i)
    (a_sub (a_sub A a_weaken) (a_compose (Syntax.q σ) a_weaken))
    (a_sub (a_sub A (a_compose a_weaken a_weaken)) (Syntax.q (Syntax.q σ)))).
  {
    apply wf_exp_eq_sym.
    eapply wf_exp_eq_trans.
    - eapply substitute_type_equality; [exact HQQ | now apply reflexive_substitution |].
      exact (type_substitution_compose _ _ _ _ _ _ _ HWs' HWs HA).
    - eapply wf_exp_eq_trans;
        [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HQQ HWs' HAW) |].
      eapply substitute_type_equality;
        [exact (wf_sub_compose _ _ _ _ _ HQQ HWs') | exact HQQE | now apply reflexive_expression].
  }
  pose proof (substitute_type _ _ _ _ _ HQQ HC) as HCsub.
  pose proof (wf_exp_eq_var_0_sub _ _ _ _ _ _ HqW HAW Hq0) as Hzero.
  assert (Hone : wf_exp_eq (a_sub (a_sub A σ) a_weaken :: a_sub A σ :: Θ)
    (a_sub (a_sub A a_weaken) (a_compose (Syntax.q σ) a_weaken))
    (a_sub (a_var 1) (Syntax.q (Syntax.q σ))) (a_var 1)).
  {
    eapply wf_exp_eq_trans;
      [exact (wf_exp_eq_var_S_sub _ _ _ _ _ _ _ _ HqW HAW Hq0 (here A Γ)) |].
    pose proof (type_of_first_variable _ _ (proj2 (substitution_contexts _ _ _ HQ))) as HX0.
    pose proof (wf_exp_eq_var_0_sub _ _ _ _ _ _ HsW HA H0) as H0E.
    pose proof (type_substitution_compose _ _ _ _ _ _ _ HQ HWs HA) as Htype.
    assert (Htype' : wf_exp_eq (a_sub A σ :: Θ) (a_typ i)
      (a_sub A (a_compose σ a_weaken)) (a_sub (a_sub A a_weaken) (Syntax.q σ))).
    {
      eapply wf_exp_eq_trans; [|exact Htype].
      eapply substitute_type_equality; [exact HsW | exact (wf_sub_eq_sym _ _ _ _ HQE) | now apply reflexive_expression].
    }
    eapply wf_exp_eq_trans; [exact (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HWt' HQ HX0) |].
    eapply convert_equality; [|exact (substitute_type _ _ _ _ _ HqW HAW) |].
    - eapply wf_exp_eq_trans.
      + exact (wf_exp_eq_sub_cong _ _ _ _ _ _ _ (convert_equality _ _ _ _ _ _ H0E
           (substitute_type _ _ _ _ _ HQ HAW) Htype') (reflexive_substitution _ _ _ HWt')).
      + eapply convert_equality.
        * exact (wf_exp_eq_var_weaken _ _ _ _ (proj1 (substitution_contexts _ _ _ HQQ)) (here (a_sub A σ) Θ)).
        * exact (substitute_type _ _ _ _ _ HWt' (substitute_type _ _ _ _ _ HQ HAW)).
        * eapply substitute_type_equality; [exact HWt' | now apply reflexive_substitution | exact HAE].
    - apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HWt' HQ HAW).
  }
  assert (HEe : wf_exp_eq (a_sub (a_sub A σ) a_weaken :: a_sub A σ :: Θ) (a_typ i)
    (a_sub (a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0)) (Syntax.q (Syntax.q σ)))
    (a_eq (a_sub (a_sub A σ) (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0))).
  {
    eapply wf_exp_eq_trans; [exact (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HQQ HC HX HY) |].
    exact (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _ Hcarry
      (convert_equality _ _ _ _ _ _ Hone HCsub Hcoerce) (convert_equality _ _ _ _ _ _ Hzero HCsub Hcoerce)).
  }
  split; [exact HE |]. split; [exact HE' |]. split; [now apply wf_exp_eq_sym |].
  destruct (lift_substitution_as_data _ _ _ _ _ _ HQQ HE HE' (wf_exp_eq_sym _ _ _ _ HEe)) as (_ & _ & HQQQ & _).
  exact HQQQ.
Qed.

Lemma lifted_extension_fusion : forall Γ Δ Θ σ τ υ i A D X,
    wf_sub Δ Γ σ -> wf_sub Θ Δ τ -> wf_sub Θ Γ υ ->
    wf_sub_eq Θ Γ (a_compose σ τ) υ ->
    wf_exp Γ (a_typ i) A -> wf_exp Δ (a_typ i) D ->
    wf_exp_eq Δ (a_typ i) D (a_sub A σ) ->
    wf_exp Θ (a_sub D τ) X ->
    wf_sub Θ (A :: Γ) (a_extend υ X) /\
    wf_sub_eq Θ (A :: Γ) (a_compose (Syntax.q σ) (a_extend τ X)) (a_extend υ X).
Proof.
  intros Γ Δ Θ σ τ υ i A D X HS HT HV HVE HA HD HDA HX.
  destruct (lift_substitution_as_data _ _ _ _ _ _ HS HA HD HDA) as (HSW & H0 & HQ & HP).
  pose proof (wf_sub_extend _ _ _ _ _ _ HT HD HX) as HTX.
  pose proof (wf_sub_weaken _ _ (proj1 (substitution_contexts _ _ _ HQ))) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HC.
  pose proof (wf_sub_compose _ _ _ _ _ HTX HSW) as HCW.
  pose proof (substitute_type _ _ _ _ _ HV HA) as HTy.
  assert (HLE : wf_sub_eq Θ Γ (a_compose (a_compose σ a_weaken) (a_extend τ X)) (a_compose σ τ)).
  {
    eapply wf_sub_eq_trans; [exact (wf_sub_eq_compose_assoc _ _ _ _ _ _ _ HS HW HTX) |].
    exact (wf_sub_eq_compose_cong _ _ _ _ _ _ _ (wf_sub_eq_p_extend _ _ _ _ _ _ HT HD HX)
      (reflexive_substitution _ _ _ HS)).
  }
  assert (HTyE : wf_exp_eq Θ (a_typ i) (a_sub D τ) (a_sub A (a_compose σ τ))).
  {
    eapply wf_exp_eq_trans; [eapply substitute_type_equality; [exact HT | now apply reflexive_substitution | exact HDA] |].
    apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HT HS HA).
  }
  split.
  - eapply wf_sub_extend; [exact HV | exact HA |].
    eapply convert_expression; [exact HX | exact HTy |].
    eapply wf_exp_eq_trans; [exact HTyE |].
    eapply substitute_type_equality; [exact HC | exact HVE | now apply reflexive_expression].
  - eapply wf_sub_eq_trans; [exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ HSW HA H0 HTX) |].
    eapply wf_sub_eq_extend_cong; [exact (wf_sub_eq_trans _ _ _ _ _ HLE HVE) | exact HA |].
    eapply convert_equality; [exact (wf_exp_eq_var_0_sub _ _ _ _ _ _ HT HD HX)
      | exact (substitute_type _ _ _ _ _ HCW HA) |].
    eapply wf_exp_eq_trans; [exact HTyE |].
    apply wf_exp_eq_sym; eapply substitute_type_equality; [exact HCW | exact HLE | now apply reflexive_expression].
Qed.

Lemma equality_motive_fusion : forall Γ Θ Ξ i A σ τ X Y P,
    wf_sub Θ Γ σ -> wf_sub Ξ Θ τ -> wf_exp Γ (a_typ i) A ->
    wf_exp Ξ (a_sub (a_sub A σ) τ) X -> wf_exp Ξ (a_sub (a_sub A σ) τ) Y ->
    wf_exp Ξ (a_eq (a_sub (a_sub A σ) τ) X Y) P ->
    let s := a_extend (a_extend (a_extend τ X) Y) P in
    let t := a_extend (a_extend (a_extend (a_compose σ τ) X) Y) P in
    wf_sub Ξ (equality_context Θ (a_sub A σ)) s /\
    wf_sub Ξ (equality_context Γ A) t /\
    wf_sub_eq Ξ (equality_context Γ A) (a_compose (Syntax.q (Syntax.q (Syntax.q σ))) s) t.
Proof.
  intros Γ Θ Ξ i A σ τ X Y P HS HT HA HX HY HP; cbn zeta.
  destruct (equality_lift_second _ _ _ _ _ HS HA) as (HA' & HAW & HAW' & HAWr & HQ & HQQ).
  destruct (equality_lift_third _ _ _ _ _ HS HA) as (HE & HE' & HEr & HQQQ).
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HC.
  destruct (equality_instantiation_at _ _ _ _ _ _ _ HT HA' HX HY) as (_ & _ & HYW & HPW).
  pose proof (wf_sub_extend _ _ _ _ _ _ HT HA' HX) as HTX.
  pose proof (convert_expression _ _ _ _ _ HY (substitute_type _ _ _ _ _ HTX HAW')
    (wf_exp_eq_sym _ _ _ _ HYW)) as HYt.
  pose proof (wf_sub_extend _ _ _ _ _ _ HTX HAW' HYt) as HTXY.
  pose proof (convert_expression _ _ _ _ _ HP (substitute_type _ _ _ _ _ HTXY HE')
    (wf_exp_eq_sym _ _ _ _ HPW)) as HPt.
  split; [exact (wf_sub_extend _ _ _ _ _ _ HTXY HE' HPt) |].
  destruct (lifted_extension_fusion _ _ _ _ _ _ _ _ _ _ HS HT HC (reflexive_substitution _ _ _ HC)
    HA HA' (reflexive_expression _ _ _ HA') HX) as (HCX & HXf).
  destruct (lifted_extension_fusion _ _ _ _ _ _ _ _ _ _ HQ HTX HCX HXf HAW HAW' HAWr HYt) as (HCXY & HYf).
  exact (lifted_extension_fusion _ _ _ _ _ _ _ _ _ _ HQQ HTXY HCXY HYf HE HE' HEr HPt).
Qed.

Lemma equality_motive_substitution_at : forall Γ Θ i A σ X Y P,
    wf_sub Θ Γ σ -> wf_exp Γ (a_typ i) A ->
    wf_exp Θ (a_sub A σ) X -> wf_exp Θ (a_sub A σ) Y -> wf_exp Θ (a_eq (a_sub A σ) X Y) P ->
    wf_sub Θ (equality_context Γ A) (a_extend (a_extend (a_extend σ X) Y) P).
Proof.
  intros Γ Θ i A σ X Y P HS HA HX HY HP.
  destruct (equality_instantiation_at _ _ _ _ _ _ _ HS HA HX HY) as (HAW & HE & HYr & HPr).
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HX) as HSX.
  pose proof (convert_expression _ _ _ _ _ HY (substitute_type _ _ _ _ _ HSX HAW)
    (wf_exp_eq_sym _ _ _ _ HYr)) as HY'.
  pose proof (wf_sub_extend _ _ _ _ _ _ HSX HAW HY') as HSXY.
  eapply wf_sub_extend; [exact HSXY | exact HE |].
  exact (convert_expression _ _ _ _ _ HP (substitute_type _ _ _ _ _ HSXY HE) (wf_exp_eq_sym _ _ _ _ HPr)).
Qed.

Lemma equality_motive_substitution_congruence : forall Γ Θ i A σ τ X X' Y Y' P P',
    wf_sub Θ Γ σ -> wf_sub_eq Θ Γ σ τ ->
    wf_exp Γ (a_typ i) A ->
    wf_exp Θ (a_sub A σ) X -> wf_exp Θ (a_sub A σ) Y ->
    wf_exp_eq Θ (a_sub A σ) X X' -> wf_exp_eq Θ (a_sub A σ) Y Y' ->
    wf_exp_eq Θ (a_eq (a_sub A σ) X Y) P P' ->
    wf_sub_eq Θ (equality_context Γ A) (a_extend (a_extend (a_extend σ X) Y) P)
      (a_extend (a_extend (a_extend τ X') Y') P').
Proof.
  intros Γ Θ i A σ τ X X' Y Y' P P' HS HT HA HX HY HXe HYe HPe.
  destruct (equality_instantiation_at _ _ _ _ _ _ _ HS HA HX HY) as (HAW & HE & HYr & HPr).
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HX) as HSX.
  pose proof (substitute_type _ _ _ _ _ HSX HAW) as HTY.
  pose proof (wf_exp_eq_sym _ _ _ _ HYr) as HYr'.
  pose proof (convert_expression _ _ _ _ _ HY HTY HYr') as HY'.
  pose proof (wf_sub_extend _ _ _ _ _ _ HSX HAW HY') as HSXY.
  eapply wf_sub_eq_extend_cong.
  - eapply wf_sub_eq_extend_cong.
    + eapply wf_sub_eq_extend_cong; [exact HT | exact HA | exact HXe].
    + exact HAW.
    + exact (convert_equality _ _ _ _ _ _ HYe HTY HYr').
  - exact HE.
  - exact (convert_equality _ _ _ _ _ _ HPe (substitute_type _ _ _ _ _ HSXY HE) (wf_exp_eq_sym _ _ _ _ HPr)).
Qed.

Lemma identity_as_variable_extension : forall Γ i A,
    wf_exp Γ (a_typ i) A ->
    wf_sub_eq (A :: Γ) (A :: Γ) (a_extend a_weaken (a_var 0)) a_id.
Proof.
  intros Γ i A HA.
  pose proof (wf_ctx_extend _ _ _ (expression_context _ _ _ HA) HA) as HG.
  pose proof (wf_sub_id _ HG) as HI.
  pose proof (wf_sub_weaken _ _ HG) as HW.
  pose proof (type_of_first_variable _ _ HG) as H0.
  apply wf_sub_eq_sym.
  eapply wf_sub_eq_trans; [exact (wf_sub_eq_extend _ _ _ _ HI) |].
  eapply wf_sub_eq_extend_cong;
    [exact (wf_sub_eq_id_compose_left _ _ _ HW) | exact HA |].
  eapply convert_equality; [exact (wf_exp_eq_sub_id _ _ _ H0) | |].
  - exact (substitute_type _ _ _ _ _ (wf_sub_compose _ _ _ _ _ HI HW) HA).
  - apply wf_exp_eq_sym; eapply substitute_type_equality;
      [exact (wf_sub_compose _ _ _ _ _ HI HW) | exact (wf_sub_eq_id_compose_left _ _ _ HW) | now apply reflexive_expression].
Qed.

Lemma equality_branch_index_data : forall Γ i A,
    wf_exp Γ (a_typ i) A ->
    let X := a_var 0 in
    let P := a_refl (a_sub A a_weaken) X in
    wf_sub (A :: Γ) (equality_context Γ A) (a_extend (a_extend a_id X) P) /\
    wf_sub_eq (A :: Γ) (equality_context Γ A) (a_extend (a_extend (a_extend a_weaken X) X) P)
      (a_extend (a_extend a_id X) P).
Proof.
  intros Γ i A HA; cbn zeta.
  pose proof (wf_ctx_extend _ _ _ (expression_context _ _ _ HA) HA) as HG.
  pose proof (wf_sub_weaken _ _ HG) as HW.
  pose proof (type_of_first_variable _ _ HG) as HX.
  pose proof (substitute_type _ _ _ _ _ HW HA) as HAW.
  pose proof (wf_refl _ _ _ _ HAW HX) as HP.
  destruct (equality_instantiation_at _ _ _ _ _ _ _ HW HA HX HX) as (_ & HE & HYr & HPr).
  pose proof (wf_sub_extend _ _ _ _ _ _ HW HA HX) as HT.
  pose proof (convert_expression _ _ _ _ _ HX (substitute_type _ _ _ _ _ HT HAW)
    (wf_exp_eq_sym _ _ _ _ HYr)) as HX'.
  pose proof (wf_sub_extend _ _ _ _ _ _ HT HAW HX') as HTX.
  pose proof (convert_expression _ _ _ _ _ HP (substitute_type _ _ _ _ _ HTX HE)
    (wf_exp_eq_sym _ _ _ _ HPr)) as HP'.
  pose proof (identity_as_variable_extension _ _ _ HA) as HEid.
  assert (HSub : wf_sub_eq (A :: Γ) (a_sub A a_weaken :: A :: Γ)
      (a_extend (a_extend a_weaken (a_var 0)) (a_var 0)) (a_extend a_id (a_var 0))).
  { eapply wf_sub_eq_extend_cong; [exact HEid | exact HAW | now apply reflexive_expression]. }
  split.
  - pose proof (wf_sub_id _ HG) as HI.
    pose proof (convert_expression _ _ _ _ _ HX (substitute_type _ _ _ _ _ HI HAW)
      (wf_exp_eq_sym _ _ _ _ (type_substitution_identity _ _ _ HAW))) as HXi.
    pose proof (wf_sub_extend _ _ _ _ _ _ HI HAW HXi) as HIX.
    eapply wf_sub_extend; [exact HIX | exact HE |].
    eapply convert_expression; [exact HP' | exact (substitute_type _ _ _ _ _ HIX HE) |].
    eapply substitute_type_equality; [exact HTX | exact HSub | now apply reflexive_expression].
  - eapply wf_sub_eq_extend_cong; [exact HSub | exact HE | now apply reflexive_expression].
Qed.

Lemma equality_motive_composition : forall Γ Θ Ξ i A σ τ X Y P,
    wf_sub Θ Γ σ -> wf_sub Ξ Θ τ -> wf_exp Γ (a_typ i) A ->
    wf_exp Θ (a_sub A σ) X -> wf_exp Θ (a_sub A σ) Y -> wf_exp Θ (a_eq (a_sub A σ) X Y) P ->
    wf_sub_eq Ξ (equality_context Γ A)
      (a_compose (a_extend (a_extend (a_extend σ X) Y) P) τ)
      (a_extend (a_extend (a_extend (a_compose σ τ) (a_sub X τ)) (a_sub Y τ)) (a_sub P τ)).
Proof.
  intros Γ Θ Ξ i A σ τ X Y P HS HT HA HX HY HP.
  destruct (equality_instantiation_at _ _ _ _ _ _ _ HS HA HX HY) as (HAW & HE & HYr & HPr).
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HX) as HSX.
  pose proof (convert_expression _ _ _ _ _ HY (substitute_type _ _ _ _ _ HSX HAW)
    (wf_exp_eq_sym _ _ _ _ HYr)) as HY'.
  pose proof (wf_sub_extend _ _ _ _ _ _ HSX HAW HY') as HSXY.
  pose proof (convert_expression _ _ _ _ _ HP (substitute_type _ _ _ _ _ HSXY HE)
    (wf_exp_eq_sym _ _ _ _ HPr)) as HP'.
  eapply wf_sub_eq_trans;
    [exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ HSXY HE HP' HT) |].
  eapply wf_sub_eq_extend_cong; [|exact HE|].
  - eapply wf_sub_eq_trans;
      [exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ HSX HAW HY' HT) |].
    eapply wf_sub_eq_extend_cong;
      [exact (wf_sub_eq_extend_compose _ _ _ _ _ _ _ _ HS HA HX HT) | exact HAW |].
    apply reflexive_expression.
    eapply convert_expression; [exact (wf_exp_sub _ _ _ _ _ HT HY') | |].
    + exact (substitute_type _ _ _ _ _ (wf_sub_compose _ _ _ _ _ HT HSX) HAW).
    + apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HT HSX HAW).
  - apply reflexive_expression.
    eapply convert_expression; [exact (wf_exp_sub _ _ _ _ _ HT HP') | |].
    + exact (substitute_type _ _ _ _ _ (wf_sub_compose _ _ _ _ _ HT HSXY) HE).
    + apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HT HSXY HE).
Qed.

Lemma equality_branch_index_fusion : forall Γ Θ i A σ X,
    wf_sub Θ Γ σ -> wf_exp Γ (a_typ i) A -> wf_exp Θ (a_sub A σ) X ->
    let sv := a_extend σ X in
    let O := a_var 0 in
    let R := a_refl (a_sub A a_weaken) O in
    wf_sub_eq Θ (equality_context Γ A)
      (a_compose (a_extend (a_extend a_id O) R) sv)
      (a_extend (a_extend (a_extend σ X) X) (a_refl (a_sub A σ) X)).
Proof.
  intros Γ Θ i A σ X HS HA HX; cbn zeta.
  destruct (equality_branch_index_data _ _ _ HA) as (HBidx & HIdx).
  pose proof (wf_sub_extend _ _ _ _ _ _ HS HA HX) as HσX.
  pose proof (proj2 (substitution_contexts _ _ _ HσX)) as HG.
  pose proof (wf_sub_weaken _ _ HG) as HW.
  pose proof (type_of_first_variable _ _ HG) as H0.
  pose proof (substitute_type _ _ _ _ _ HW HA) as HAW.
  pose proof (wf_refl _ _ _ _ HAW H0) as HR.
  pose proof (wf_sub_compose _ _ _ _ _ HσX HW) as Hcmp.
  pose proof (wf_sub_eq_p_extend _ _ _ _ _ _ HS HA HX) as HP.
  pose proof (substitute_weakening _ _ _ _ _ _ _ _ HS HA HA HX) as HAWr.
  pose proof (substitute_type _ _ _ _ _ HσX HAW) as HAWs.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (type_substitution_compose _ _ _ _ _ _ _ HσX HW HA) as HAWc.
  pose proof (wf_exp_eq_var_0_sub _ _ _ _ _ _ HS HA HX) as H0e.
  pose proof (substitute_type _ _ _ _ _ Hcmp HA) as HcmpT.
  assert (Htype : wf_exp_eq Θ (a_typ i) (a_sub A σ) (a_sub A (a_compose a_weaken (a_extend σ X)))).
  { apply wf_exp_eq_sym; eapply substitute_type_equality; [exact Hcmp | exact HP | now apply reflexive_expression]. }
  pose proof (convert_equality _ _ _ _ _ _ H0e HcmpT Htype) as H0c.
  pose proof (convert_equality _ _ _ _ _ _ H0e HAWs (wf_exp_eq_sym _ _ _ _ HAWr)) as H0s.
  pose proof (wf_exp_sub _ _ _ _ _ HσX H0) as H0w.
  pose proof (convert_expression _ _ _ _ _ H0w HcmpT (wf_exp_eq_sym _ _ _ _ HAWc)) as H0t.
  assert (HProof : wf_exp_eq Θ (a_eq (a_sub A (a_compose a_weaken (a_extend σ X)))
      (a_sub (a_var 0) (a_extend σ X)) (a_sub (a_var 0) (a_extend σ X)))
      (a_sub (a_refl (a_sub A a_weaken) (a_var 0)) (a_extend σ X)) (a_refl (a_sub A σ) X)).
  {
    pose proof (wf_eq _ _ _ _ _ HcmpT H0t H0t) as Hqq.
    eapply wf_exp_eq_trans.
    - eapply convert_equality; [exact (wf_exp_eq_refl_sub _ _ _ _ _ _ HσX HAW H0) | exact Hqq |].
      eapply wf_exp_eq_trans; [exact (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HσX HAW H0 H0) |].
      eapply wf_exp_eq_eq_cong; [apply wf_exp_eq_sym; exact HAWc | now apply reflexive_expression | now apply reflexive_expression].
    - eapply convert_equality;
        [eapply wf_exp_eq_refl_cong; [exact HAWr | exact H0s] | exact Hqq |].
      eapply wf_exp_eq_eq_cong; [apply wf_exp_eq_sym; exact HAWc | now apply reflexive_expression | now apply reflexive_expression].
  }
  eapply wf_sub_eq_trans.
  - eapply wf_sub_eq_compose_cong; [exact (reflexive_substitution _ _ _ HσX) | exact (wf_sub_eq_sym _ _ _ _ HIdx)].
  - eapply wf_sub_eq_trans;
      [exact (equality_motive_composition _ _ _ _ _ _ _ _ _ _ HW HσX HA H0 H0 HR) |].
    exact (equality_motive_substitution_congruence _ _ _ _ _ _ _ _ _ _ _ _ Hcmp HP HA H0t H0t H0c H0c HProof).
Qed.

Lemma equality_lift_branch_type : forall Γ Θ i j A B σ,
    wf_sub Θ Γ σ -> wf_exp Γ (a_typ i) A -> wf_exp (equality_context Γ A) (a_typ j) B ->
    wf_exp_eq (a_sub A σ :: Θ) (a_typ j)
      (a_sub (equality_branch_type A B) (Syntax.q σ))
      (equality_branch_type (a_sub A σ) (a_sub B (Syntax.q (Syntax.q (Syntax.q σ))))).
Proof.
  intros Γ Θ i j A B σ HS HA HB.
  destruct (equality_lift_second _ _ _ _ _ HS HA) as (HA' & _ & _ & _ & HQ & _).
  destruct (equality_lift_third _ _ _ _ _ HS HA) as (_ & _ & _ & HQQQ).
  destruct (equality_branch_index_data _ _ _ HA) as (HBidx & _).
  destruct (equality_branch_index_data _ _ _ HA') as (HBidx' & HIdx').
  pose proof (wf_sub_weaken _ _ (proj1 (substitution_contexts _ _ _ HQ))) as HW.
  pose proof (wf_sub_compose _ _ _ _ _ HW HS) as HT.
  pose proof (type_of_first_variable _ _ (proj1 (substitution_contexts _ _ _ HQ))) as HX.
  pose proof (substitute_type _ _ _ _ _ HW HA') as HxT.
  pose proof (type_substitution_compose _ _ _ _ _ _ _ HW HS HA) as Hxe.
  pose proof (convert_expression _ _ _ _ _ HX (substitute_type _ _ _ _ _ HT HA)
    (wf_exp_eq_sym _ _ _ _ Hxe)) as HXc.
  pose proof (wf_refl _ _ _ _ HxT HX) as HRe.
  destruct (equality_motive_fusion _ _ _ _ _ _ _ _ _ _ HS HW HA HX HX HRe) as (Hidx3 & Hc3 & HF).
  pose proof (equality_branch_index_fusion _ _ _ _ _ _ HT HA HXc) as Hleft.
  pose proof (wf_sub_compose _ _ _ _ _ HQ HBidx) as HL.
  pose proof (wf_exp_eq_refl_cong _ _ _ _ _ _ (wf_exp_eq_sym _ _ _ _ Hxe) (reflexive_expression _ _ _ HX)) as HRee.
  assert (Hlr : wf_sub_eq (a_sub A σ :: Θ) (equality_context Γ A)
    (a_compose (a_extend (a_extend a_id (a_var 0)) (a_refl (a_sub A a_weaken) (a_var 0))) (Syntax.q σ))
    (a_compose (Syntax.q (Syntax.q (Syntax.q σ))) (a_extend (a_extend a_id (a_var 0))
       (a_refl (a_sub (a_sub A σ) a_weaken) (a_var 0))))).
  {
    eapply wf_sub_eq_trans; [exact Hleft |].
    eapply wf_sub_eq_trans.
    - eapply equality_motive_substitution_congruence;
        [exact HT | now apply reflexive_substitution | exact HA | exact HXc | exact HXc
        | now apply reflexive_expression | now apply reflexive_expression |].
      eapply convert_equality; [apply wf_exp_eq_sym; exact HRee | exact (wf_eq _ _ _ _ _ (substitute_type _ _ _ _ _ HT HA) HXc HXc) |].
      eapply wf_exp_eq_eq_cong; [exact (wf_exp_eq_sym _ _ _ _ Hxe) | exact (reflexive_expression _ _ _ HX) | exact (reflexive_expression _ _ _ HX)].
    - eapply wf_sub_eq_trans; [apply wf_sub_eq_sym; exact HF |].
      exact (wf_sub_eq_compose_cong _ _ _ _ _ _ _ HIdx' (reflexive_substitution _ _ _ HQQQ)).
  }
  unfold equality_branch_type.
  eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HQ HBidx HB) |].
  eapply wf_exp_eq_trans; [|exact (type_substitution_compose _ _ _ _ _ _ _ HBidx' HQQQ HB)].
  eapply substitute_type_equality; [exact HL | exact Hlr | now apply reflexive_expression].
Qed.

Lemma equality_reflexive_motives_agree : forall Γ i j A B ρ a x y z b c S,
    wf_exp (equality_context Γ A) (a_typ j) B ->
    env_related Γ ρ ρ -> eval_exp A ρ a ->
    at_type i a a S ->
    S x x -> S y y ->
    semantic_member (d_eq a x y) (d_refl z) ->
    eval_exp B (extend_three ρ z z (d_refl z)) c ->
    eval_exp B (extend_three ρ x y (d_refl z)) b ->
    exists T, at_type j c b T.
Proof.
  intros Γ i j A B ρ a x y z b c S HB Hρ Ha HT Hx Hy (l & V & HV & HR) Hc Hb.
  pose proof (model_eq _ _ _ _ _ _ _ _ HT Hx Hy) as HEq.
  pose proof (proj1 (at_type_coherent_l _ _ _ _ _ _ _ HV HEq _ _) HR) as HR'.
  inversion HR'; subst.
  assert (Hp : eq_rel S z z x y (d_refl z) (d_refl z)) by (apply eq_rel_refl; assumption).
  pose proof (relate_equality_context _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hρ Ha Ha HT H2 H3 Hp) as HEnv.
  destruct fundamental_evaluation as (_ & _ & Hexp & _).
  destruct (from_universe _ _ _ _ _ (proj1 (Hexp _ _ _ HB) _ _ HEnv))
    as (c' & b' & Hc' & Hb' & R & Hrel).
  resolve_eval. exists R; exact Hrel.
Qed.

Lemma equality_terms_change_type : forall Θ i A B X Y P,
    wf_exp Θ (a_typ i) B -> wf_exp_eq Θ (a_typ i) A B ->
    wf_exp Θ A X -> wf_exp Θ A Y -> wf_exp Θ (a_eq A X Y) P ->
    wf_exp Θ B X /\ wf_exp Θ B Y /\ wf_exp Θ (a_eq B X Y) P.
Proof.
  intros Θ i A B X Y P HB HE HX HY HP.
  pose proof (convert_expression _ _ _ _ _ HX HB HE) as HX'.
  pose proof (convert_expression _ _ _ _ _ HY HB HE) as HY'.
  split; [exact HX' |]. split; [exact HY' |].
  exact (convert_expression _ _ _ _ _ HP (wf_eq _ _ _ _ _ HB HX' HY')
    (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _ HE (reflexive_expression _ _ _ HX) (reflexive_expression _ _ _ HY))).
Qed.

Lemma equality_lift_instance_type : forall Γ Θ i j A B σ X Y P,
    wf_sub Θ Γ σ -> wf_exp Γ (a_typ i) A -> wf_exp (equality_context Γ A) (a_typ j) B ->
    wf_exp Θ (a_sub A σ) X -> wf_exp Θ (a_sub A σ) Y -> wf_exp Θ (a_eq (a_sub A σ) X Y) P ->
    wf_exp_eq Θ (a_typ j) (equality_result_type (a_sub B (Syntax.q (Syntax.q (Syntax.q σ)))) X Y P)
      (a_sub B (a_extend (a_extend (a_extend σ X) Y) P)).
Proof.
  intros Γ Θ i j A B σ X Y P HS HA HB HX HY HP.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HA'.
  pose proof (expression_context _ _ _ HA') as HΘ.
  pose proof (wf_sub_id _ HΘ) as HID.
  pose proof (substitute_type _ _ _ _ _ HID HA') as HAI.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_identity _ _ _ HA')) as HAE.
  destruct (equality_terms_change_type _ _ _ _ _ _ _ HAI HAE HX HY HP) as (HX' & HY' & HP').
  destruct (equality_motive_fusion _ _ _ _ _ _ _ _ _ _ HS HID HA HX' HY' HP') as (HSN & HST & HSE).
  destruct (equality_lift_third _ _ _ _ _ HS HA) as (_ & _ & _ & HQQQ).
  pose proof (wf_sub_eq_id_compose_left _ _ _ HS) as HCI.
  pose proof (wf_sub_compose _ _ _ _ _ HID HS) as HSID.
  pose proof (substitute_type _ _ _ _ _ HSID HA) as HAS.
  assert (HAT : wf_exp_eq Θ (a_typ i) (a_sub A σ) (a_sub A (a_compose σ a_id))).
  { apply wf_exp_eq_sym; eapply substitute_type_equality; [exact HSID | exact HCI | now apply reflexive_expression]. }
  destruct (equality_terms_change_type _ _ _ _ _ _ _ HAS HAT HX HY HP) as (HXc & HYc & HPc).
  pose proof (equality_motive_substitution_congruence _ _ _ _ _ _ _ _ _ _ _ _ HSID HCI HA HXc HYc
    (reflexive_expression _ _ _ HXc) (reflexive_expression _ _ _ HYc) (reflexive_expression _ _ _ HPc)) as HCT.
  unfold equality_result_type.
  eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HSN HQQQ HB) |].
  eapply substitute_type_equality; [exact (wf_sub_compose _ _ _ _ _ HSN HQQQ) | exact (wf_sub_eq_trans _ _ _ _ _ HSE HCT)
    | now apply reflexive_expression].
Qed.

Lemma equality_result_type_substitution : forall Γ Θ i j A B σ X Y P,
    wf_sub Θ Γ σ -> wf_exp Γ (a_typ i) A -> wf_exp (equality_context Γ A) (a_typ j) B ->
    wf_exp Γ A X -> wf_exp Γ A Y -> wf_exp Γ (a_eq A X Y) P ->
    wf_exp_eq Θ (a_typ j) (a_sub (equality_result_type B X Y P) σ)
      (a_sub B (a_extend (a_extend (a_extend σ (a_sub X σ)) (a_sub Y σ)) (a_sub P σ))).
Proof.
  intros Γ Θ i j A B σ X Y P HS HA HB HX HY HP.
  pose proof (expression_context _ _ _ HA) as HΓ.
  pose proof (wf_sub_id _ HΓ) as HI.
  pose proof (substitute_type _ _ _ _ _ HI HA) as HAI.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_identity _ _ _ HA)) as HAE.
  destruct (equality_terms_change_type _ _ _ _ _ _ _ HAI HAE HX HY HP) as (HX' & HY' & HP').
  pose proof (equality_motive_substitution_at _ _ _ _ _ _ _ _ HI HA HX' HY' HP') as Ht.
  pose proof (equality_motive_composition _ _ _ _ _ _ _ _ _ _ HI HS HA HX' HY' HP') as HE.
  pose proof (wf_sub_compose _ _ _ _ _ HS HI) as HIσ.
  pose proof (wf_sub_eq_id_compose_right _ _ _ HS) as HIE.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HAs.
  pose proof (wf_exp_sub _ _ _ _ _ HS HX) as HXσ.
  pose proof (wf_exp_sub _ _ _ _ _ HS HY) as HYσ.
  pose proof (convert_expression _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HS HP) (wf_eq _ _ _ _ _ HAs HXσ HYσ)
      (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HS HA HX HY)) as HPσ.
  assert (HAT : wf_exp_eq Θ (a_typ i) (a_sub A σ) (a_sub A (a_compose a_id σ))).
  { apply wf_exp_eq_sym; eapply substitute_type_equality; [exact HIσ | exact HIE | now apply reflexive_expression]. }
  destruct (equality_terms_change_type _ _ _ _ _ _ _ (substitute_type _ _ _ _ _ HIσ HA) HAT
    HXσ HYσ HPσ) as (HXc & HYc & HPc).
  pose proof (equality_motive_substitution_congruence _ _ _ _ _ _ _ _ _ _ _ _ HIσ HIE HA HXc HYc
    (reflexive_expression _ _ _ HXc) (reflexive_expression _ _ _ HYc) (reflexive_expression _ _ _ HPc)) as HIC.
  unfold equality_result_type.
  eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HS Ht HB) |].
  eapply substitute_type_equality;
    [exact (wf_sub_compose _ _ _ _ _ HS Ht) | exact (wf_sub_eq_trans _ _ _ _ _ HE HIC) | now apply reflexive_expression].
Qed.

Lemma native_equality_branches : forall Γ Θ i j A B BR σ,
    wf_sub Θ Γ σ -> wf_exp Γ (a_typ i) A -> wf_exp (equality_context Γ A) (a_typ j) B ->
    wf_exp (A :: Γ) (equality_branch_type A B) BR ->
    let D := a_sub A σ in
    let C := a_sub B (Syntax.q (Syntax.q (Syntax.q σ))) in
    wf_exp (equality_context Θ D) (a_typ j) C /\
    wf_exp (D :: Θ) (equality_branch_type D C) (a_sub BR (Syntax.q σ)).
Proof.
  intros Γ Θ i j A B BR σ HS HA HB HBR; cbn zeta.
  destruct (equality_lift_third _ _ _ _ _ HS HA) as (_ & _ & _ & HQQQ).
  destruct (equality_lift_second _ _ _ _ _ HS HA) as (HA' & _ & _ & _ & HQ & _).
  destruct (equality_branch_index_data _ _ _ HA') as (HBi & _).
  pose proof (substitute_type _ _ _ _ _ HQQQ HB) as HC.
  split; [exact HC |].
  eapply convert_expression;
    [exact (wf_exp_sub _ _ _ _ _ HQ HBR) | exact (substitute_type _ _ _ _ _ HBi HC) |].
  exact (equality_lift_branch_type _ _ _ _ _ _ _ HS HA HB).
Qed.

Lemma glued_term_semantic_member : forall U Γ A M a m,
    glued_term U Γ A M a m -> semantic_member a m.
Proof.
  intros U Γ A M a m (i & R & GA & GM).
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HA.
  pose proof (weakening_identity _ (expression_context _ _ _ HA)) as HID.
  exact (proj1 (proj2 (candidate_has_invariants _ _ _ _ _ _ GA _ _ _ _ HID GM))).
Qed.

Definition equality_recursion_realizes k Θ A B BR σ ρ X Y P a x y p :=
  exists b r, eval_exp B (extend_three ρ x y p) b /\ eval_eqrec a B BR x y p ρ r /\
    glued_term (gluing_universes k) Θ (a_sub B (a_extend (a_extend (a_extend σ X) Y) P))
      (a_eqrec (a_sub A σ) (a_sub B (Syntax.q (Syntax.q (Syntax.q σ)))) (a_sub BR (Syntax.q σ)) X Y P) b r.

Lemma gluing_equality_reflexive_case : forall k Γ Θ i j A B BR σ ρ X Y P Z a x y z S b Q,
    glued_environment (gluing_universes k) Θ Γ σ ρ ->
    wf_exp Γ (a_typ i) A -> eval_exp A ρ a ->
    wf_exp (equality_context Γ A) (a_typ j) B ->
    wf_exp (A :: Γ) (equality_branch_type A B) BR ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (equality_branch_type A B) BR ->
    at_type i a a S -> S x x -> S y y ->
    glued_term (gluing_universes k) Θ (a_sub A σ) Z a z ->
    wf_exp Θ (a_sub A σ) X -> wf_exp Θ (a_sub A σ) Y -> wf_exp Θ (a_eq (a_sub A σ) X Y) P ->
    wf_exp_eq Θ (a_sub A σ) X Z -> wf_exp_eq Θ (a_sub A σ) Y Z ->
    wf_exp_eq Θ (a_eq (a_sub A σ) X Y) P (a_refl (a_sub A σ) Z) ->
    semantic_member (d_eq a x y) (d_refl z) ->
    eval_exp B (extend_three ρ x y (d_refl z)) b ->
    glued_type (gluing_universes k) Θ j (a_sub B (a_extend (a_extend (a_extend σ X) Y) P)) b Q ->
    equality_recursion_realizes k Θ A B BR σ ρ X Y P a x y (d_refl z).
Proof.
  intros k Γ Θ i j A B BR σ ρ X Y P Z a x y z S b Q HE HA Ha HB HBR HBRg HS Hx Hy GZ
    HX HY HP HXZ HYZ HPR Hmem Hb GB.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HT.
  pose proof (glued_term_typing _ _ _ _ _ _ GZ) as HZ.
  pose proof (substitute_type _ _ _ _ _ HT HA) as HD.
  pose proof (wf_refl _ _ _ _ HD HZ) as HR.
  pose proof (glued_environment_extend _ _ _ _ _ _ _ _ _ _ HU HC HE HA Ha GZ) as HEZ.
  destruct (HBRg _ _ _ HEZ) as (c & r & Hc & Hr & GR).
  assert (Hc' : eval_exp B (extend_three ρ z z (d_refl z)) c).
  {
    unfold equality_branch_type in Hc; inversion Hc; subst.
    assert (HI : eval_sub (a_extend (a_extend a_id (a_var 0)) (a_refl (a_sub A a_weaken) (a_var 0)))
      (extend_env ρ z) (extend_three ρ z z (d_refl z))).
    { repeat first [apply eval_sub_extend | apply eval_sub_id | apply eval_exp_refl | apply eval_exp_var]. }
    resolve_eval. assumption.
  }
  destruct (equality_reflexive_motives_agree _ _ _ _ _ _ _ _ _ _ _ _ _ HB
    (glued_environment_semantic _ _ _ _ _ HE) Ha HS Hx Hy Hmem Hc' Hb) as (V & HV).
  destruct (native_equality_branches _ _ _ _ _ _ _ _ HT HA HB HBR) as (HB' & HBR').
  pose proof (expression_context _ _ _ HD) as HΘ.
  pose proof (wf_sub_id _ HΘ) as HID.
  pose proof (wf_sub_compose _ _ _ _ _ HID HT) as HTI.
  pose proof (wf_sub_eq_id_compose_left _ _ _ HT) as HTIe.
  pose proof (substitute_type _ _ _ _ _ HTI HA) as HATI.
  assert (HATe : wf_exp_eq Θ (a_typ i) (a_sub A σ) (a_sub A (a_compose σ a_id))).
  { apply wf_exp_eq_sym; eapply substitute_type_equality; [exact HTI | exact HTIe | now apply reflexive_expression]. }
  pose proof (convert_expression _ _ _ _ _ HZ (substitute_type _ _ _ _ _ HID HD)
    (wf_exp_eq_sym _ _ _ _ (type_substitution_identity _ _ _ HD))) as HZi.
  destruct (lifted_extension_fusion _ _ _ _ _ _ _ _ _ _ HT HID HT HTIe HA HD
    (reflexive_expression _ _ _ HD) HZi) as (HTZ & HQIe).
  pose proof (instantiate_type _ _ _ _ HD HZ) as HIZ.
  destruct (equality_lift_second _ _ _ _ _ HT HA) as (_ & _ & _ & _ & HQ & _).
  destruct (equality_branch_index_data _ _ _ HA) as (HBI & _).
  pose proof (substitute_type _ _ _ _ _ HBI HB) as HBT.
  pose proof (equality_branch_index_fusion _ _ _ _ _ _ HT HA HZ) as HBIe.
  pose proof (equality_motive_substitution_congruence _ _ _ _ _ _ _ _ _ _ _ _ HT (reflexive_substitution _ _ _ HT)
    HA HX HY HXZ HYZ HPR) as Hmote.
  pose proof (equality_motive_substitution_at _ _ _ _ _ _ _ _ HT HA HX HY HP) as Hmot.
  pose proof (equality_motive_substitution_at _ _ _ _ _ _ _ _ HT HA HZ HZ HR) as HmotZ.
  pose proof (substitute_type_equality _ _ _ _ _ _ _ Hmot Hmote (reflexive_expression _ _ _ HB)) as Hte.
  pose proof (substitute_type _ _ _ _ _ HmotZ HB) as Htz.
  assert (Htr : wf_exp_eq Θ (a_typ j) (a_sub (equality_branch_type A B) (a_extend σ Z))
    (a_sub B (a_extend (a_extend (a_extend σ Z) Z) (a_refl (a_sub A σ) Z)))).
  {
    eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HTZ HBI HB) |].
    eapply substitute_type_equality; [exact (wf_sub_compose _ _ _ _ _ HTZ HBI) | exact HBIe | now apply reflexive_expression].
  }
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GR Htz Htr) as GR'.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GB) as Hout.
  pose proof (equality_lift_instance_type _ _ _ _ _ _ _ _ _ _ HT HA HB HX HY HP) as HE0.
  pose proof (equality_lift_instance_type _ _ _ _ _ _ _ _ _ _ HT HA HB HZ HZ HR) as HE1.
  assert (HE2 : wf_exp_eq Θ (a_sub B (a_extend (a_extend (a_extend σ X) Y) P))
     (a_eqrec (a_sub A σ) (a_sub B (Syntax.q (Syntax.q (Syntax.q σ)))) (a_sub BR (Syntax.q σ)) X Y P)
     (a_sub BR (a_extend σ Z))).
  {
    eapply wf_exp_eq_trans.
    - eapply convert_equality; [|exact Hout|exact HE0].
      eapply wf_exp_eq_eqrec_cong;
        [exact HD | exact HX | exact HY | exact (reflexive_expression _ _ _ HD) | exact HXZ | exact HYZ
        | exact (reflexive_expression _ _ _ HB') | exact (reflexive_expression _ _ _ HBR') | exact HPR].
    - eapply wf_exp_eq_trans.
      + eapply convert_equality; [exact (wf_exp_eq_eqrec_beta _ _ _ _ _ _ _ HD HZ HB' HBR') | exact Hout |].
        exact (wf_exp_eq_trans _ _ _ _ _ HE1 (wf_exp_eq_sym _ _ _ _ Hte)).
      + eapply convert_equality.
        * eapply wf_exp_eq_trans.
          -- apply wf_exp_eq_sym; exact (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HIZ HQ HBR).
          -- exact (wf_exp_eq_sub_cong _ _ _ _ _ _ _ (reflexive_expression _ _ _ HBR) HQIe).
        * exact Hout.
        * eapply wf_exp_eq_trans.
          -- eapply substitute_type_equality; [exact (wf_sub_compose _ _ _ _ _ HIZ HQ) | exact HQIe | now apply reflexive_expression].
          -- exact (wf_exp_eq_trans _ _ _ _ _ Htr (wf_exp_eq_sym _ _ _ _ Hte)).
  }
  pose proof (wf_eqrec _ _ _ _ _ _ _ _ _ HD HX HY HB' HBR' HP) as HM.
  pose proof (glued_term_semantic_member _ _ _ _ _ _ GR') as (l & T & HL & HTmem).
  exists b, r; split; [exact Hb |]. split; [now apply eval_eqrec_refl |].
  eapply glued_term_change; [exact HU | exact HC | exact GR' | exact Hout | exact (wf_exp_eq_sym _ _ _ _ Hte)
    | exact (convert_expression _ _ _ _ _ HM Hout HE0) | exact (wf_exp_eq_sym _ _ _ _ HE2) | exact HV |].
  exact (proj2 (at_type_coherent_l _ _ _ _ _ _ _ HV HL _ _) HTmem).
Qed.

Lemma lift_substitution_congruence_as : forall Γ Θ i A D σ τ,
    wf_sub Θ Γ σ -> wf_sub_eq Θ Γ σ τ ->
    wf_exp Γ (a_typ i) A -> wf_exp Θ (a_typ i) D ->
    wf_exp_eq Θ (a_typ i) D (a_sub A σ) ->
    wf_sub_eq (D :: Θ) (A :: Γ) (Syntax.q σ) (Syntax.q τ).
Proof.
  intros Γ Θ i A D σ τ HS HE HA HD HD'.
  destruct (lift_substitution_as_data _ _ _ _ _ _ HS HA HD HD') as (_ & HX & HL & _).
  eapply wf_sub_eq_extend_cong; [|exact HA|exact (reflexive_expression _ _ _ HX)].
  eapply wf_sub_eq_compose_cong; [|exact HE].
  apply reflexive_substitution, wf_sub_weaken.
  exact (proj1 (substitution_contexts _ _ _ HL)).
Qed.

Lemma equality_lift_composition : forall Γ Θ Ξ i A σ τ,
    wf_sub Θ Γ σ -> wf_sub Ξ Θ τ -> wf_exp Γ (a_typ i) A ->
    let D := a_sub A σ in
    let E := a_sub D τ in
    let s := a_compose σ τ in
    wf_sub_eq (E :: Ξ) (A :: Γ) (a_compose (Syntax.q σ) (Syntax.q τ)) (Syntax.q s) /\
    wf_sub_eq (equality_context Ξ E) (equality_context Γ A)
      (a_compose (Syntax.q (Syntax.q (Syntax.q σ))) (Syntax.q (Syntax.q (Syntax.q τ))))
      (Syntax.q (Syntax.q (Syntax.q s))).
Proof.
  intros Γ Θ Ξ i A σ τ HS HT HA; cbn zeta.
  destruct (equality_lift_second _ _ _ _ _ HS HA) as (HD & HAW & HDW & HAWD & HQS & HQQS).
  destruct (equality_lift_second _ _ _ _ _ HT HD) as (HE & _ & HEW & HDE & HQT & HQQT).
  destruct (equality_lift_third _ _ _ _ _ HS HA) as (HQA & HQD & HDA & HQQQS).
  destruct (equality_lift_third _ _ _ _ _ HT HD) as (_ & HQE & HED & HQQQT).
  pose proof (lift_substitution_composition_as _ _ _ _ _ _ _ _ _ HS HT HA HD HE
    (reflexive_expression _ _ _ HD) (reflexive_expression _ _ _ HE)) as HC1.
  split; [exact HC1 |].
  pose proof (lift_substitution_composition_as _ _ _ _ _ _ _ _ _ HQS HQT HAW HDW HEW HAWD HDE) as HC2.
  pose proof (wf_sub_compose _ _ _ _ _ HQT HQS) as HX1.
  assert (Hd2 : wf_exp_eq (a_sub (a_sub A σ) τ :: Ξ) (a_typ i) (a_sub (a_sub (a_sub A σ) τ) a_weaken)
    (a_sub (a_sub A a_weaken) (a_compose (Syntax.q σ) (Syntax.q τ)))).
  {
    eapply wf_exp_eq_trans; [exact HDE |].
    eapply wf_exp_eq_trans.
    - eapply substitute_type_equality; [exact HQT | now apply reflexive_substitution | exact HAWD].
    - apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HQT HQS HAW).
  }
  pose proof (lift_substitution_congruence_as _ _ _ _ _ _ _ HX1 HC1 HAW HEW Hd2) as HC2'.
  pose proof (wf_sub_eq_trans _ _ _ _ _ HC2 HC2') as HC2''.
  pose proof (lift_substitution_composition_as _ _ _ _ _ _ _ _ _ HQQS HQQT HQA HQD HQE HDA HED) as HC3.
  eapply wf_sub_eq_trans; [exact HC3 |].
  eapply lift_substitution_congruence_as; [eapply wf_sub_compose; [exact HQQT | exact HQQS] | exact HC2'' | exact HQA | exact HQE |].
  eapply wf_exp_eq_trans; [exact HED |].
  eapply wf_exp_eq_trans.
  - eapply substitute_type_equality; [exact HQQT | now apply reflexive_substitution | exact HDA].
  - apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HQQT HQQS HQA).
Qed.

Lemma equality_glued_fresh_environment : forall k Γ Θ i A σ ρ a R,
    glued_environment (gluing_universes k) Θ Γ σ ρ ->
    wf_exp Γ (a_typ i) A -> eval_exp A ρ a ->
    glued_type (gluing_universes k) Θ i (a_sub A σ) a R ->
    let u := d_neut a (d_var (length Θ)) in
    let v := d_neut a (d_var (S (length Θ))) in
    glued_environment (gluing_universes k) (equality_context Θ (a_sub A σ)) (equality_context Γ A)
      (Syntax.q (Syntax.q (Syntax.q σ))) (extend_three ρ u v (d_neut (d_eq a u v) (d_var (S (S (length Θ)))))).
Proof.
  intros k Γ Θ i A σ ρ a R HE HA Ha GA; cbn zeta.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (gluing_universes_weaken k) as HW.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  destruct (equality_lift_second _ _ _ _ _ HS HA) as (HA' & HAW & HAW' & HAWr & HQ & HQQ).
  destruct (equality_lift_third _ _ _ _ _ HS HA) as (HEt & HEt' & HEr & HQQQ).
  pose proof (lift_glued_environment _ _ _ _ _ _ _ _ _ HU HC HW HE HA Ha GA) as HE1.
  pose proof (weakening_drop _ _ (proj1 (substitution_contexts _ _ _ HQ))) as HW1.
  pose proof (weakening_drop _ _ (proj1 (substitution_contexts _ _ _ HQQ))) as HW2.
  pose proof (weakening_compose _ _ _ _ _ HW2 HW1) as HWW.
  pose proof (glued_type_shift _ _ _ _ _ _ _ _ GA HW1) as GW1.
  pose proof (glued_type_shift _ _ _ _ _ _ _ _ GA HWW) as GW2.
  set (D := a_sub A σ).
  set (Θ2 := a_sub D a_weaken :: D :: Θ).
  set (u := d_neut a (d_var (length Θ))).
  set (v := d_neut a (d_var (S (length Θ)))).
  assert (HAWv : eval_exp (a_sub A a_weaken) (extend_env ρ u) a).
  { eapply eval_exp_sub; [apply eval_sub_weaken | exact Ha]. }
  pose proof (lift_glued_environment_as _ _ _ _ _ _ _ _ _ _ HU HC HW HE1 HAW HAWv GW1 HAWr) as HE2.
  pose proof (proj1 (substitution_contexts _ _ _ HQQ)) as HG2.
  pose proof (variable_neutral_under_weakening _ _ _ HG2 (there _ _ _ _ (here D Θ))) as Hnu.
  pose proof (variable_neutral_under_weakening _ _ _ HG2 (here (a_sub D a_weaken) (D :: Θ))) as Hnv.
  change (neutral_under_weakening Θ2 (a_sub (a_sub D a_weaken) a_weaken) (a_var 1)
    (d_var (length Θ2 - 1 - 1))) in Hnu.
  change (neutral_under_weakening Θ2 (a_sub (a_sub D a_weaken) a_weaken) (a_var 0)
    (d_var (length Θ2 - 0 - 1))) in Hnv.
  replace (length Θ2 - 1 - 1) with (length Θ) in Hnu by (unfold Θ2; cbn; lia).
  replace (length Θ2 - 0 - 1) with (S (length Θ)) in Hnv by (unfold Θ2; cbn; lia).
  destruct (equality_lift_inf_type _ _ _ HA') as (HD2 & HX & HY).
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_compose _ _ _ _ _ _ _
    (weakening_is_typed _ _ _ HW2) (weakening_is_typed _ _ _ HW1) HA')) as HWT.
  pose proof (convert_neutral_under_weakening _ _ _ _ _ _ HD2 HWT Hnu) as HNu.
  pose proof (convert_neutral_under_weakening _ _ _ _ _ _ HD2 HWT Hnv) as HNv.
  pose proof (reflect_glued_term _ _ _ _ _ _ _ _ HU GW2 HX HNu) as GX.
  pose proof (reflect_glued_term _ _ _ _ _ _ _ _ HU GW2 HY HNv) as GY.
  assert (HEv : eval_exp (a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0))
                    (extend_env (extend_env ρ u) v) (d_eq a u v)).
  {
    eapply eval_exp_eq.
    - eapply eval_exp_sub; [eapply eval_sub_compose; apply eval_sub_weaken | exact Ha].
    - apply eval_exp_var.
    - apply eval_exp_var.
  }
  destruct (semantically_typed_code _ _ _ _ _ HEt (glued_environment_semantic _ _ _ _ _ HE2) HEv) as (S0 & Hsem).
  pose proof (glued_type_eq _ _ _ _ _ _ _ _ _ _ _ Hsem GW2 HX HY
    (glued_term_at_weakening _ _ _ _ _ _ _ _ HU HC HW GW2 GX)
    (glued_term_at_weakening _ _ _ _ _ _ _ _ HU HC HW GW2 GY)) as GE.
  exact (lift_glued_environment_as _ _ _ _ _ _ _ _ _ _ HU HC HW HE2 HEt HEv GE HEr).
Qed.

Lemma quote_native_equality_recursion : forall k Γ Θ i j A B BR σ ρ X Y P a x y n R,
    j < k -> glued_environment (gluing_universes k) Θ Γ σ ρ ->
    wf_exp Γ (a_typ i) A -> eval_exp A ρ a ->
    wf_exp (equality_context Γ A) (a_typ j) B ->
    typing_respects_gluing (gluing_universes k) (equality_context Γ A) (a_typ j) B ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (equality_branch_type A B) BR ->
    glued_type (gluing_universes k) Θ i (a_sub A σ) a R ->
    glued_term (gluing_universes k) Θ (a_sub A σ) X a x ->
    glued_term (gluing_universes k) Θ (a_sub A σ) Y a y ->
    quoted_neutral Θ (a_eq (a_sub A σ) X Y) P n ->
    quoted_neutral Θ (equality_result_type (a_sub B (Syntax.q (Syntax.q (Syntax.q σ)))) X Y P)
      (a_eqrec (a_sub A σ) (a_sub B (Syntax.q (Syntax.q (Syntax.q σ)))) (a_sub BR (Syntax.q σ)) X Y P)
      (d_eqrec ρ a B BR x y n).
Proof.
  intros k Γ Θ i j A B BR σ ρ X Y P a x y n R Hk HE HA Ha HB HBg HBRg GA GX GY HP.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (gluing_universes_weaken k) as HW.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HDA.
  pose proof (expression_context _ _ _ HDA) as HΘ.
  pose proof (equality_glued_fresh_environment _ _ _ _ _ _ _ _ _ HE HA Ha GA) as HE3.
  destruct (extract_glued_code _ _ _ _ _ _ _ Hk HE3 HBg) as (b & S & Hb & GB).
  pose proof (lift_glued_environment _ _ _ _ _ _ _ _ _ HU HC HW HE HA Ha GA) as HE1.
  destruct (HBRg _ _ _ HE1) as (bc & r & Hbc & Hr & GR).
  assert (Hbc' : eval_exp B (extend_three ρ (d_neut a (d_var (length Θ)))
      (d_neut a (d_var (length Θ))) (d_refl (d_neut a (d_var (length Θ))))) bc).
  {
    unfold equality_branch_type in Hbc; inversion Hbc; subst.
    set (u := d_neut a (d_var (length Θ))).
    assert (HI : eval_sub (a_extend (a_extend a_id (a_var 0)) (a_refl (a_sub A a_weaken) (a_var 0)))
      (extend_env ρ u) (extend_three ρ u u (d_refl u))).
    { repeat first [apply eval_sub_extend | apply eval_sub_id | apply eval_exp_refl | apply eval_exp_var]. }
    resolve_eval. assumption.
  }
  pose proof (glued_type_well_formed _ _ _ _ _ _ GB) as HBT.
  destruct (equality_branch_index_data _ _ _ HDA) as (HBI & _).
  pose proof (substitute_type _ _ _ _ _ HBI HBT) as HBRT.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GR HBRT (equality_lift_branch_type _ _ _ _ _ _ _ HS HA HB)) as GR'.
  assert (Hquote : forall Γ0 k0 A0 a0 R0, glued_type (gluing_universes k) Γ0 k0 A0 a0 R0 ->
    quoted_type Γ0 k0 A0 a0).
  {
    intros Γ0 k0 A0 a0 R0 G0.
    pose proof (glued_type_well_formed _ _ _ _ _ _ G0) as H0.
    eapply quote_type_conversion; [apply wf_exp_eq_sym; exact (type_substitution_identity _ _ _ H0) |].
    exact (quotation_of_type _ _ _ _ (proj1 (quoted_candidate_reflects _ _ _ _ _ _ HU G0)) _ _
      (weakening_identity _ (expression_context _ _ _ H0))).
  }
  eapply quote_neutral_eqrec; [exact HDA | exact (glued_term_typing _ _ _ _ _ _ GX) | exact (glued_term_typing _ _ _ _ _ _ GY)
    | exact (Hquote _ _ _ _ _ GA) | exact (glued_term_quote _ _ _ _ _ _ GX) | exact (glued_term_quote _ _ _ _ _ _ GY)
    | exact Hb | exact (Hquote _ _ _ _ _ GB) | exact Hbc' | exact Hr | exact (glued_term_quote _ _ _ _ _ _ GR') | exact HP].
Qed.

Lemma equality_recursor_weaken_syntax : forall Γ Θ Ξ i j A B BR σ τ X Y P,
    wf_sub Θ Γ σ -> wf_sub Ξ Θ τ ->
    wf_exp Γ (a_typ i) A -> wf_exp (equality_context Γ A) (a_typ j) B ->
    wf_exp (A :: Γ) (equality_branch_type A B) BR ->
    wf_exp Θ (a_sub A σ) X -> wf_exp Θ (a_sub A σ) Y -> wf_exp Θ (a_eq (a_sub A σ) X Y) P ->
    let s := a_compose σ τ in
    let R t U V Q := a_eqrec (a_sub A t) (a_sub B (Syntax.q (Syntax.q (Syntax.q t)))) (a_sub BR (Syntax.q t)) U V Q in
    let F := a_sub B (a_extend (a_extend (a_extend s (a_sub X τ)) (a_sub Y τ)) (a_sub P τ)) in
    wf_exp Ξ (a_typ j) F /\
    wf_exp_eq Ξ (a_typ j) (a_sub (a_sub B (a_extend (a_extend (a_extend σ X) Y) P)) τ) F /\
    wf_exp_eq Ξ F (a_sub (R σ X Y P) τ) (R s (a_sub X τ) (a_sub Y τ) (a_sub P τ)).
Proof.
  intros Γ Θ Ξ i j A B BR σ τ X Y P HS HT HA HB HBR HX HY HP; cbn zeta.
  pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HC.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HD.
  pose proof (substitute_type _ _ _ _ _ HT HD) as HE.
  pose proof (substitute_type _ _ _ _ _ HC HA) as HAc.
  pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_compose _ _ _ _ _ _ _ HT HS HA)) as HAE.
  pose proof (wf_exp_sub _ _ _ _ _ HT HX) as HXt.
  pose proof (wf_exp_sub _ _ _ _ _ HT HY) as HYt.
  pose proof (convert_expression _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HT HP) (wf_eq _ _ _ _ _ HE HXt HYt)
    (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HT HD HX HY)) as HPt.
  destruct (equality_motive_fusion _ _ _ _ _ _ _ _ _ _ HS HT HA HXt HYt HPt) as (HSN & HSF & HSFq).
  pose proof (substitute_type _ _ _ _ _ HSF HB) as HF.
  pose proof (equality_motive_substitution_at _ _ _ _ _ _ _ _ HS HA HX HY HP) as HM.
  pose proof (equality_motive_composition _ _ _ _ _ _ _ _ _ _ HS HT HA HX HY HP) as HMC.
  split; [exact HF |]. split.
  - eapply wf_exp_eq_trans; [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HT HM HB) |].
    eapply substitute_type_equality; [exact (wf_sub_compose _ _ _ _ _ HT HM) | exact HMC | now apply reflexive_expression].
  - destruct (native_equality_branches _ _ _ _ _ _ _ _ HS HA HB HBR) as (HB' & HBR').
    destruct (native_equality_branches _ _ _ _ _ _ _ _ HT HD HB' HBR') as (HB'' & HBR'').
    destruct (equality_lift_composition _ _ _ _ _ _ _ HS HT HA) as (HQE & HQQQE).
    destruct (equality_lift_second _ _ _ _ _ HS HA) as (_ & _ & _ & _ & HQ & _).
    destruct (equality_lift_second _ _ _ _ _ HT HD) as (_ & _ & _ & _ & HQT & _).
    destruct (equality_lift_third _ _ _ _ _ HS HA) as (_ & _ & _ & HQQQ).
    destruct (equality_lift_third _ _ _ _ _ HT HD) as (_ & _ & _ & HQQQT).
    assert (HFE : wf_exp_eq Ξ (a_typ j)
      (a_sub (a_sub B (Syntax.q (Syntax.q (Syntax.q σ)))) (a_extend (a_extend (a_extend τ (a_sub X τ)) (a_sub Y τ)) (a_sub P τ)))
      (a_sub B (a_extend (a_extend (a_extend (a_compose σ τ) (a_sub X τ)) (a_sub Y τ)) (a_sub P τ)))).
    {
      eapply wf_exp_eq_trans;
        [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HSN HQQQ HB) |].
      eapply substitute_type_equality; [exact (wf_sub_compose _ _ _ _ _ HSN HQQQ) | exact HSFq | now apply reflexive_expression].
    }
    eapply wf_exp_eq_trans.
    + eapply convert_equality;
        [exact (wf_exp_eq_eqrec_sub _ _ _ _ _ _ _ _ _ _ _ HT HD HX HY HB' HBR' HP) | exact HF | exact HFE].
    + eapply convert_equality; [|exact HF|].
      * eapply wf_exp_eq_eqrec_cong;
          [exact HE | exact HXt | exact HYt | exact HAE
          | exact (reflexive_expression _ _ _ HXt) | exact (reflexive_expression _ _ _ HYt) | | | exact (reflexive_expression _ _ _ HPt)].
        -- eapply wf_exp_eq_trans;
             [apply wf_exp_eq_sym; exact (type_substitution_compose _ _ _ _ _ _ _ HQQQT HQQQ HB) |].
           eapply substitute_type_equality;
             [exact (wf_sub_compose _ _ _ _ _ HQQQT HQQQ) | exact HQQQE | now apply reflexive_expression].
        -- eapply convert_equality.
           ++ eapply wf_exp_eq_trans.
              ** apply wf_exp_eq_sym; exact (wf_exp_eq_sub_compose _ _ _ _ _ _ _ HQT HQ HBR).
              ** exact (wf_exp_eq_sub_cong _ _ _ _ _ _ _ (reflexive_expression _ _ _ HBR) HQE).
           ++ destruct (equality_branch_index_data _ _ _ HE) as (Hidx & _).
              exact (substitute_type _ _ _ _ _ Hidx HB'').
           ++ destruct (equality_branch_index_data _ _ _ HA) as (Hidx & _).
              pose proof (substitute_type _ _ _ _ _ Hidx HB) as HBRT.
              eapply wf_exp_eq_trans;
                [exact (type_substitution_compose _ _ _ _ _ _ _ HQT HQ HBRT) |].
              eapply wf_exp_eq_trans.
              ** eapply substitute_type_equality; [exact HQT | now apply reflexive_substitution |].
                 exact (equality_lift_branch_type _ _ _ _ _ _ _ HS HA HB).
              ** exact (equality_lift_branch_type _ _ _ _ _ _ _ HT HD HB').
      * exact (wf_exp_eq_trans _ _ _ _ _
          (equality_lift_instance_type _ _ _ _ _ _ _ _ _ _ HT HD HB' HXt HYt HPt) HFE).
Qed.

Lemma gluing_equality_neutral_case : forall k Γ Θ i j A B BR σ ρ X Y P a x y e n R b Q,
    j < k -> glued_environment (gluing_universes k) Θ Γ σ ρ ->
    wf_exp Γ (a_typ i) A -> eval_exp A ρ a ->
    wf_exp (equality_context Γ A) (a_typ j) B ->
    wf_exp (A :: Γ) (equality_branch_type A B) BR ->
    typing_respects_gluing (gluing_universes k) (equality_context Γ A) (a_typ j) B ->
    typing_respects_gluing (gluing_universes k) (A :: Γ) (equality_branch_type A B) BR ->
    glued_type (gluing_universes k) Θ i (a_sub A σ) a R ->
    glued_term (gluing_universes k) Θ (a_sub A σ) X a x ->
    glued_term (gluing_universes k) Θ (a_sub A σ) Y a y ->
    wf_exp Θ (a_eq (a_sub A σ) X Y) P ->
    neutral_under_weakening Θ (a_eq (a_sub A σ) X Y) P n ->
    eval_exp B (extend_three ρ x y (d_neut e n)) b ->
    glued_type (gluing_universes k) Θ j (a_sub B (a_extend (a_extend (a_extend σ X) Y) P)) b Q ->
    equality_recursion_realizes k Θ A B BR σ ρ X Y P a x y (d_neut e n).
Proof.
  intros k Γ Θ i j A B BR σ ρ X Y P a x y e n R b Q Hk HE HA Ha HB HBR HBg HBRg GA GX GY HP Hne Hb GB.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (gluing_universes_weaken k) as HW.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  pose proof (glued_term_typing _ _ _ _ _ _ GX) as HX.
  pose proof (glued_term_typing _ _ _ _ _ _ GY) as HY.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GB) as HBT.
  pose proof (glued_type_well_formed _ _ _ _ _ _ GA) as HDA.
  pose proof (equality_lift_instance_type _ _ _ _ _ _ _ _ _ _ HS HA HB HX HY HP) as HBI.
  destruct (native_equality_branches _ _ _ _ _ _ _ _ HS HA HB HBR) as (HB' & HBR').
  exists b, (d_neut b (d_eqrec ρ a B BR x y n)); split; [exact Hb |]. split.
  - exact (eval_eqrec_neut _ _ _ _ _ _ _ _ _ Hb).
  - eapply reflect_glued_term; [exact HU | exact GB | |].
    + exact (convert_expression _ _ _ _ _ (wf_eqrec _ _ _ _ _ _ _ _ _ HDA HX HY HB' HBR' HP) HBT HBI).
    + intros Ξ τ Hτ.
      pose proof (weakening_is_typed _ _ _ Hτ) as HT.
      pose proof (glued_environment_weaken _ _ _ _ _ HU HC HW HE _ _ Hτ) as HE'.
      pose proof (wf_sub_compose _ _ _ _ _ HT HS) as HS'.
      pose proof (substitute_type _ _ _ _ _ HS' HA) as HA'.
      pose proof (wf_exp_eq_sym _ _ _ _ (type_substitution_compose _ _ _ _ _ _ _ HT HS HA)) as HAe.
      pose proof (glued_type_shift _ _ _ _ _ _ _ _ GA Hτ) as GAw.
      pose proof (glued_type_convert _ _ _ _ _ _ _ GAw HA' HAe) as GA'.
      pose proof (glued_term_weaken _ _ _ _ _ _ _ _ HU HC HW Hτ GX) as GXw.
      pose proof (glued_term_weaken _ _ _ _ _ _ _ _ HU HC HW Hτ GY) as GYw.
      pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GXw HA' HAe) as GX'.
      pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GYw HA' HAe) as GY'.
      pose proof (glued_term_typing _ _ _ _ _ _ GX') as HX'.
      pose proof (glued_term_typing _ _ _ _ _ _ GY') as HY'.
      pose proof (wf_eq _ _ _ _ _ HA' HX' HY') as HEt.
      pose proof (wf_exp_sub _ _ _ _ _ HT HX) as HXw.
      pose proof (wf_exp_sub _ _ _ _ _ HT HY) as HYw.
      pose proof (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HT HDA HX HY) as HEe.
      pose proof (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _ HAe (reflexive_expression _ _ _ HXw)
        (reflexive_expression _ _ _ HYw)) as HEe'.
      pose proof (quote_neutral_type_conversion _ _ _ _ _ _ HEt (wf_exp_eq_trans _ _ _ _ _ HEe HEe')
        (Hne _ _ Hτ)) as HPq.
      pose proof (convert_expression _ _ _ _ _ (wf_exp_sub _ _ _ _ _ HT HP) HEt (wf_exp_eq_trans _ _ _ _ _ HEe HEe')) as HP'.
      pose proof (quote_native_equality_recursion _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hk
        HE' HA Ha HB HBg HBRg GA' GX' GY' HPq) as HQR.
      destruct (equality_recursor_weaken_syntax _ _ _ _ _ _ _ _ _ _ _ _ _ HS HT HA HB HBR HX HY HP) as (HFT & HFe & HRe).
      pose proof (equality_lift_instance_type _ _ _ _ _ _ _ _ _ _ HS' HA HB HX' HY' HP') as HFE.
      eapply quote_neutral_type_conversion; [exact (substitute_type _ _ _ _ _ HT HBT) | exact (wf_exp_eq_sym _ _ _ _ HFe) |].
      eapply quote_neutral_conversion; [exact HRe |].
      exact (quote_neutral_type_conversion _ _ _ _ _ _ HFT HFE HQR).
Qed.

Lemma gluing_equality_eliminator : equality_eliminator_respects_gluing.
Proof.
  intros k Γ i j A B BR X Y P Hik Hjk HA HX HY HB HBR HP HAg HXg HYg HBg HBRg HPg Θ σ ρ HE.
  pose proof (gluing_universes_quote k) as HU.
  pose proof (gluing_universes_coherent k) as HC.
  pose proof (gluing_universes_weaken k) as HW.
  pose proof (glued_environment_typing _ _ _ _ _ HE) as HS.
  destruct (gluing_equality_data _ _ _ _ _ _ _ _ _ Hik HA HX HY HAg HXg HYg HE)
    as (a & x & y & R & S & Ha & Hx & Hy & Hsem & GA & GX & GY).
  destruct (HPg _ _ _ HE) as (d & p & Hd & Hp & GP).
  assert (Hd' : eval_exp (a_eq A X Y) ρ (d_eq a x y)) by now apply eval_exp_eq.
  pose proof (exp_unique _ _ _ Hd _ Hd') as He; subst d.
  pose proof (substitute_type _ _ _ _ _ HS HA) as HDA.
  pose proof (glued_term_typing _ _ _ _ _ _ GX) as HXw.
  pose proof (glued_term_typing _ _ _ _ _ _ GY) as HYw.
  pose proof (wf_eq _ _ _ _ _ HDA HXw HYw) as HEw.
  pose proof (glued_term_type_change _ _ _ _ _ _ _ _ GP HEw (wf_exp_eq_eq_sub _ _ _ _ _ _ _ HS HA HX HY)) as GP'.
  pose proof (glued_term_typing _ _ _ _ _ _ GP') as HPw.
  pose proof (glued_equality_motive_environment _ _ _ _ _ _ _ _ _ _ _ _ _ _ HE HA Ha GX GY GP') as HEq.
  destruct (extract_glued_code _ _ _ _ _ _ _ Hjk HEq HBg) as (b & Q & Hb & GB).
  pose proof (glued_type_eq _ _ _ _ _ _ _ _ _ _ _ Hsem GA HXw HYw
    (glued_term_at_weakening _ _ _ _ _ _ _ _ HU HC HW GA GX)
    (glued_term_at_weakening _ _ _ _ _ _ _ _ HU HC HW GA GY)) as GE.
  pose proof (candidate_at_identity _ _ _ _ _ _ _ _ HU HC GE GP') as (_ & Hmem & _ & Hcore).
  pose proof (type_substitution_identity _ _ _ HEw) as HEwI.
  assert (HCase : equality_recursion_realizes k Θ A B BR σ ρ (a_sub X σ) (a_sub Y σ) (a_sub P σ) a x y p).
  {
    destruct Hcore as [(e & n & Ep & HN) | (Z & z & Ep & GZ0 & HZX & HZY & HR)]; subst p.
    - eapply gluing_equality_neutral_case;
        [exact Hjk | exact HE | exact HA | exact Ha | exact HB | exact HBR | exact HBg | exact HBRg
        | exact GA | exact GX | exact GY | exact HPw | | exact Hb | exact GB].
      exact (convert_neutral_under_weakening _ _ _ _ _ _ HEw HEwI HN).
    - destruct (glued_type_semantic _ _ _ _ _ _ GA) as (T & HT).
      destruct (glued_term_semantic_member _ _ _ _ _ _ GX) as (l & V & HV & Hm).
      destruct (glued_term_semantic_member _ _ _ _ _ _ GY) as (l' & V' & HV' & Hm').
      pose proof (proj1 (at_type_coherent_l _ _ _ _ _ _ _ HV HT _ _) Hm) as Hxx.
      pose proof (proj1 (at_type_coherent_l _ _ _ _ _ _ _ HV' HT _ _) Hm') as Hyy.
      pose proof (glued_at_candidate_identity _ _ _ _ _ _ _ _ GA GZ0) as GZ.
      pose proof (glued_term_typing _ _ _ _ _ _ GZ) as HZ.
      pose proof (type_substitution_identity _ _ _ HDA) as HDAi.
      pose proof (expression_context _ _ _ HDA) as HΘ.
      pose proof (wf_sub_id _ HΘ) as HId.
      pose proof (substitute_type _ _ _ _ _ HId HDA) as HDi.
      pose proof (convert_expression _ _ _ _ _ HZ HDi (wf_exp_eq_sym _ _ _ _ HDAi)) as HZi.
      pose proof (convert_equality _ _ _ _ _ _ HZX HDA HDAi) as HZE1.
      pose proof (convert_equality _ _ _ _ _ _ HZY HDA HDAi) as HZE2.
      pose proof (wf_exp_eq_trans _ _ _ _ _ HZE1 (wf_exp_eq_sub_id _ _ _ HXw)) as HZx.
      pose proof (wf_exp_eq_trans _ _ _ _ _ HZE2 (wf_exp_eq_sub_id _ _ _ HYw)) as HZy.
      assert (HPR : wf_exp_eq Θ (a_eq (a_sub A σ) (a_sub X σ) (a_sub Y σ)) (a_sub P σ) (a_refl (a_sub A σ) Z)).
      {
        eapply wf_exp_eq_trans; [exact (convert_equality _ _ _ _ _ _ HR HEw HEwI) |].
        eapply convert_equality.
        - exact (wf_exp_eq_refl_cong _ _ _ _ _ _ HDAi (reflexive_expression _ _ _ HZi)).
        - exact HEw.
        - exact (wf_exp_eq_eq_cong _ _ _ _ _ _ _ _ HDAi
            (convert_equality _ _ _ _ _ _ HZx HDi (wf_exp_eq_sym _ _ _ _ HDAi))
            (convert_equality _ _ _ _ _ _ HZy HDi (wf_exp_eq_sym _ _ _ _ HDAi))).
      }
      eapply gluing_equality_reflexive_case;
        [exact HE | exact HA | exact Ha | exact HB | exact HBR | exact HBRg | exact HT | exact Hxx | exact Hyy
        | exact GZ | exact HXw | exact HYw | exact HPw | exact (wf_exp_eq_sym _ _ _ _ HZx)
        | exact (wf_exp_eq_sym _ _ _ _ HZy) | exact HPR | exact Hmem | exact Hb | exact GB].
  }
  destruct HCase as (b' & r & Hb' & Hr & GR).
  pose proof (exp_unique _ _ _ Hb' _ Hb) as Ee; subst b'.
  pose proof (equality_motive_substitution _ _ _ _ _ _ HA HX HY HP) as Hs0.
  pose proof (substitute_type _ _ _ _ _ HS (substitute_type _ _ _ _ _ Hs0 HB)) as Ht.
  pose proof (equality_result_type_substitution _ _ _ _ _ _ _ _ _ _ HS HA HB HX HY HP) as Hte.
  pose proof (wf_exp_eq_eqrec_sub _ _ _ _ _ _ _ _ _ _ _ HS HA HX HY HB HBR HP) as Hree.
  exists b, r; split; [eapply eval_equality_result_type; eassumption |]. split.
  - eapply eval_exp_eqrec; [exact Ha | exact Hx | exact Hy | exact Hp | exact Hr].
  - eapply glued_term_expression_change;
      [exact HU | exact HC | exact (glued_term_type_change _ _ _ _ _ _ _ _ GR Ht (wf_exp_eq_sym _ _ _ _ Hte))
      | exact (wf_exp_sub _ _ _ _ _ HS (wf_eqrec _ _ _ _ _ _ _ _ _ HA HX HY HB HBR HP)) |].
    eapply convert_equality; [apply wf_exp_eq_sym; exact Hree | exact Ht | exact (wf_exp_eq_sym _ _ _ _ Hte)].
Qed.

End Gluing.

Theorem soundness : forall {Γ M A},
    {{ Γ ⊢ M : A }} ->
    exists W, nbe Γ M A W /\ {{ Γ ⊢ M ≈ W : A }}.
Proof.
  intros Γ M A HM.
  exact (Gluing.soundness_from_eliminators Gluing.gluing_natural_eliminator
    Gluing.gluing_equality_eliminator Γ M A HM).
Qed.
