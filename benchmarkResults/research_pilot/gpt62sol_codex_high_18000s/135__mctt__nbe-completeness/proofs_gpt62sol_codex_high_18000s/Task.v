From Stdlib Require Import List PeanoNat Arith.Wf_nat Lia.
From Mctt.Core Require Import Base.

From Mctt.Core.Semantic Require Export NbE.

Import Domain_Notations.

Local Hint Constructors eval_exp eval_sub eval_app eval_natrec eval_fst eval_snd
  eval_eqrec read_nf read_ne read_typ initial_env nbe : mctt.

(* Evaluation and readback are deterministic. *)

Local Lemma fst_unique : forall m u v, eval_fst m u -> eval_fst m v -> u = v.
Proof. intros m u v H K; destruct H; inversion K; reflexivity. Qed.

Local Lemma evaluation_unique :
  (forall e ρ m, eval_exp e ρ m -> forall m', eval_exp e ρ m' -> m = m') /\
  (forall A Z S m ρ r, eval_natrec A Z S m ρ r ->
      forall r', eval_natrec A Z S m ρ r' -> r = r') /\
  (forall f x m, eval_app f x m -> forall m', eval_app f x m' -> m = m') /\
  (forall f m, eval_snd f m -> forall m', eval_snd f m' -> m = m') /\
  (forall a B R x y n ρ m, eval_eqrec a B R x y n ρ m ->
      forall m', eval_eqrec a B R x y n ρ m' -> m = m') /\
  (forall σ ρ ξ, eval_sub σ ρ ξ -> forall ξ', eval_sub σ ρ ξ' -> ξ = ξ').
Proof.
  apply eval_mut_ind; intros;
    match goal with H : _ |- _ => inversion H; clear H; subst end;
    repeat match goal with
    | IH : forall v, ?P v -> ?u = v, H : ?P ?w |- _ =>
        first [constr_eq u w; fail 1 | let E := fresh in
          pose proof (IH _ H) as E; first [subst w | clear E; fail 1]]
    end; eauto using fst_unique.
Qed.

Local Lemma exp_unique : forall e ρ m v,
  eval_exp e ρ m -> eval_exp e ρ v -> m = v.
Proof. exact (fun e ρ m v H => proj1 evaluation_unique e ρ m H v). Qed.

Local Lemma app_unique : forall f x m v,
  eval_app f x m -> eval_app f x v -> m = v.
Proof. exact (fun f x m v H => proj1 (proj2 (proj2 evaluation_unique)) f x m H v). Qed.

Local Lemma snd_unique : forall f m v,
  eval_snd f m -> eval_snd f v -> m = v.
Proof. exact (fun f m v H => proj1 (proj2 (proj2 (proj2 evaluation_unique))) f m H v). Qed.

Local Ltac same_eval :=
  repeat match goal with
  | H : eval_exp ?e ?ρ ?a, K : eval_exp ?e ?ρ ?b |- _ =>
      first [constr_eq a b; fail 1 | is_var b; let E := fresh in
        pose proof (exp_unique _ _ _ _ H K) as E; subst b; clear K]
  | H : eval_app ?f ?x ?a, K : eval_app ?f ?x ?b |- _ =>
      first [constr_eq a b; fail 1 | is_var b; let E := fresh in
        pose proof (app_unique _ _ _ _ H K) as E; subst b; clear K]
  | H : eval_fst ?f ?a, K : eval_fst ?f ?b |- _ =>
      first [constr_eq a b; fail 1 | is_var b; let E := fresh in
        pose proof (fst_unique _ _ _ H K) as E; subst b; clear K]
  | H : eval_snd ?f ?a, K : eval_snd ?f ?b |- _ =>
      first [constr_eq a b; fail 1 | is_var b; let E := fresh in
        pose proof (snd_unique _ _ _ H K) as E; subst b; clear K]
  end.

Local Notation "ρ ▻ a" := (extend_env ρ a) (at level 25, left associativity).
Local Notation "'Ev' B ρ a b" := (eval_exp B (ρ ▻ a) b) (at level 10, B at level 0, ρ at level 0, a at level 0, b at level 0).
Local Definition drel := domain -> domain -> Prop.
Local Definition equiv (R S : drel) := forall x y, R x y <-> S x y.
Local Infix "≃" := equiv (at level 70, no associativity).
Local Definition incl (R S : drel) := forall x y, R x y -> S x y.
Local Definition per (R : drel) :=
  (forall x y, R x y -> R y x) /\ (forall x y z, R x y -> R y z -> R x z).

Local Lemma per_left R : per R -> forall x y, R x y -> R x x.
Proof. unfold per; firstorder. Qed.
Local Lemma per_right R : per R -> forall x y, R x y -> R y y.
Proof. unfold per; firstorder. Qed.
Local Lemma equiv_per R S : R ≃ S -> per S -> per R.
Proof.
  intros E [Sym Tr]; split.
  - intros x y H; apply E, Sym, E, H.
  - intros x y z H K; apply E; eapply Tr; [apply E, H | apply E, K].
Qed.

(* Related neutrals read back to the same syntax at every depth. *)

Local Definition neutral (m n : domain_ne) :=
  forall s, exists W, read_ne s m W /\ read_ne s n W.

Local Lemma neutral_per :
  (forall m n, neutral m n -> neutral n m) /\
  (forall m n p, neutral m n -> neutral n p -> neutral m p).
Proof.
  split.
  - unfold neutral; firstorder.
  - unfold neutral. intros m n p H K s.
    destruct (H s) as (W & Hm & Hn), (K s) as (W' & Hn' & Hp).
    assert (D :
      (forall s m w, read_nf s m w -> forall w', read_nf s m w' -> w = w') /\
      (forall s m w, read_ne s m w -> forall w', read_ne s m w' -> w = w') /\
      (forall s m w, read_typ s m w -> forall w', read_typ s m w' -> w = w')).
    { apply read_mut_ind; intros;
        match goal with H : _ |- _ => inversion H; clear H; subst end;
        same_eval; f_equal; eauto. }
    replace W' with W in Hp by (eapply (proj1 (proj2 D)); eassumption).
    eauto.
Qed.

Local Definition neutral_at : drel := fun x y =>
  exists a b m n, x = d_neut a m /\ y = d_neut b n /\ neutral m n.

Local Lemma neutral_at_per : per neutral_at.
Proof.
  destruct neutral_per as [Sym Trans].
  split; unfold neutral_at.
  - intros x y (? & ? & ? & ? & -> & -> & ?); eauto 8.
  - intros x y z (? & ? & ? & ? & -> & -> & ?) (? & ? & ? & ? & E & -> & ?).
    inversion E; subst; eauto 8.
Qed.

Inductive nat_rel : drel :=
| nat_rel_zero : nat_rel d_zero d_zero
| nat_rel_succ x y : nat_rel x y -> nat_rel (d_succ x) (d_succ y)
| nat_rel_ne a b m n : neutral m n -> nat_rel (d_neut a m) (d_neut b n).

Local Lemma nat_per : per nat_rel.
Proof.
  destruct neutral_per as [Sym Trans].
  split.
  - intros x y H; induction H; constructor; auto.
  - intros x y z H; revert z; induction H; intros z K; inversion K; subst;
      constructor; eauto.
Qed.

Local Definition pi_rel (R : drel) (S : domain -> domain -> drel) : drel :=
  fun f g => forall x y, R x y ->
    exists u v, eval_app f x u /\ eval_app g y v /\ S x y u v.

Local Definition sigma_rel (R : drel) (S : domain -> domain -> drel) : drel :=
  fun f g => exists x y u v, eval_fst f x /\ eval_fst g y /\
    R x y /\ eval_snd f u /\ eval_snd g v /\ S x y u v.

Inductive eq_rel (R : drel) (l r : domain) : drel :=
| eq_rel_refl x y : R x y -> R x l -> R x r -> eq_rel R l r (d_refl x) (d_refl y)
| eq_rel_ne a b m n : neutral m n -> eq_rel R l r (d_neut a m) (d_neut b n).

Local Lemma eq_per R l r : per R -> per (eq_rel R l r).
Proof.
  intros [Sym Trans]; destruct neutral_per as [NS NT].
  split.
  - intros x y H; destruct H; constructor; eauto.
  - intros x y z H; revert z; destruct H; intros z H'; inversion H'; subst;
      constructor; eauto.
Qed.

(* A type interpretation records the common relation for its two endpoints.
   At a universe, the relation is supplied by the lower levels. *)
Inductive ty (U : nat -> drel) (i : nat) : domain -> domain -> drel -> Prop :=
| ty_univ j R : j < i -> R ≃ U j -> ty U i (d_univ j) (d_univ j) R
| ty_nat R : R ≃ nat_rel -> ty U i d_nat d_nat R
| ty_ne a b m n R : neutral m n -> R ≃ neutral_at ->
    ty U i (d_neut a m) (d_neut b n) R
| ty_pi a a' ρ ρ' B B' R S T :
    ty U i a a' R ->
    (forall x y, R x y -> exists b b', Ev B ρ x b /\ Ev B' ρ' y b') ->
    (forall x y b b', R x y -> Ev B ρ x b -> Ev B' ρ' y b' ->
      ty U i b b' (S x y)) ->
    T ≃ pi_rel R S -> ty U i (d_pi a ρ B) (d_pi a' ρ' B') T
| ty_sigma a a' ρ ρ' B B' R S T :
    ty U i a a' R ->
    (forall x y, R x y -> exists b b', Ev B ρ x b /\ Ev B' ρ' y b') ->
    (forall x y b b', R x y -> Ev B ρ x b -> Ev B' ρ' y b' ->
      ty U i b b' (S x y)) ->
    T ≃ sigma_rel R S -> ty U i (d_sigma a ρ B) (d_sigma a' ρ' B') T
| ty_eq a a' l l' r r' R T :
    ty U i a a' R -> R l l' -> R r r' ->
    T ≃ eq_rel R l r -> ty U i (d_eq a l r) (d_eq a' l' r') T.

Local Lemma equiv_trans R S T : R ≃ S -> S ≃ T -> R ≃ T.
Proof. intros E F x y; rewrite (E x y), (F x y); reflexivity. Qed.

Local Lemma ty_change U i a b R S :
  ty U i a b R -> S ≃ R -> ty U i a b S.
Proof. intros H E; destruct H; econstructor; eauto using equiv_trans. Qed.

Local Hint Resolve ty_change : mctt.

Local Definition family_equiv R (S T : domain -> domain -> drel) :=
  forall x y, R x y -> S x y ≃ T x y.

Local Lemma pi_equiv R R' S S' :
  R ≃ R' -> family_equiv R S S' -> pi_rel R S ≃ pi_rel R' S'.
Proof.
  intros E F f g; split; intros H x y K.
  - apply E in K. destruct (H _ _ K) as (u & v & ? & ? & ?).
    exists u, v; repeat split; auto. apply (F _ _ K); assumption.
  - assert (K' : R' x y) by (apply E; assumption).
    destruct (H _ _ K') as (u & v & ? & ? & ?).
    exists u, v; repeat split; auto. apply (F _ _ K); assumption.
Qed.

Local Lemma sigma_equiv R R' S S' :
  R ≃ R' -> family_equiv R S S' -> sigma_rel R S ≃ sigma_rel R' S'.
Proof.
  intros E F f g; split;
    intros (x & y & u & v & Fx & Fy & H & Fu & Fv & K);
    exists x, y, u, v; repeat split; auto.
  - apply E; assumption.
  - apply (F _ _ H); assumption.
  - apply E; assumption.
  - apply (F x y); [apply E |]; assumption.
Qed.

Local Lemma eq_equiv R R' l l' r r' :
  R ≃ R' ->
  (forall x, R x l <-> R' x l') ->
  (forall x, R x r <-> R' x r') ->
  eq_rel R l r ≃ eq_rel R' l' r'.
Proof.
  intros E L G x y; split; intro H; destruct H.
  - constructor; [apply (E x y) | apply L | apply G]; assumption.
  - constructor; assumption.
  - constructor; [apply (E x y) | apply L | apply G]; assumption.
  - constructor; assumption.
Qed.

Local Lemma endpoint_equiv R R' l l' :
  per R -> R ≃ R' -> R l l' -> forall x, R x l <-> R' x l'.
Proof.
  intros [Sym Tr] E H x; rewrite <- (E x l'); split; eauto.
Qed.

Local Definition family_per R (S : domain -> domain -> drel) :=
  (forall x y, R x y -> per (S x y)) /\
  (forall x y u v, R x y -> R u v -> x = u \/ y = v -> S x y ≃ S u v).

Local Lemma family_swap R S : per R -> family_per R S ->
  forall x y, R x y -> S x y ≃ S y x.
Proof.
  intros HR [_ E] x y H.
  assert (K : R x x) by (eapply per_left; eassumption).
  assert (K' : R y x) by (apply HR; assumption).
  eapply equiv_trans with (S := S x x); eapply E; eauto.
Qed.

Local Lemma pi_per R S : per R -> family_per R S -> per (pi_rel R S).
Proof.
  intros HR HF. destruct HF as [HP HE]. split.
  - intros f g H x y Hxy.
    assert (Hyx : R y x) by (apply HR; assumption).
    destruct (H _ _ Hyx) as (u & v & Hu & Hv & Huv).
    exists v, u; repeat split; auto.
    apply (family_swap R S HR (conj HP HE) _ _ Hxy).
    apply (HP _ _ Hyx); assumption.
  - intros f g h H K x y Hxy.
    assert (Hyy : R y y) by (eapply per_right; eassumption).
    destruct (H _ _ Hxy) as (u & v & Hu & Hv & Huv).
    destruct (K _ _ Hyy) as (v' & w & Hv' & Hw & Hvw).
    same_eval. exists u, w; repeat split; auto.
    eapply (proj2 (HP _ _ Hxy)); [eassumption |].
    apply (HE x y y y); auto.
Qed.

Local Lemma sigma_per R S : per R -> family_per R S -> per (sigma_rel R S).
Proof.
  intros HR HF. destruct HF as [HP HE]. split.
  - intros f g (x & y & u & v & Fx & Fy & Hxy & Fu & Fv & Huv).
    exists y, x, v, u; repeat split; auto.
    + apply HR; assumption.
    + apply (family_swap R S HR (conj HP HE) _ _ Hxy).
      apply (HP _ _ Hxy); assumption.
  - intros f g h (x & y & u & v & Fx & Fy & Hxy & Fu & Fv & Huv)
                  (y' & z & v' & w & Fy' & Fz & Hyz & Fv' & Fw & Hvw).
    same_eval.
    assert (Hxz : R x z) by (eapply (proj2 HR); eassumption).
    exists x, z, u, w; repeat split; auto.
    apply (proj2 (HP _ _ Hxz) u v w).
    + apply (HE x z x y); auto.
    + apply (HE x z y z); auto.
Qed.

Local Definition lower_per U i := forall k, k < i -> per (U k).
Local Definition lower_equiv U V i j :=
  forall k, k < i -> k < j -> U k ≃ V k.

Local Definition coherent U i a b R :=
  forall V j c d T, lower_equiv U V i j -> a = c \/ b = d ->
    ty V j c d T -> R ≃ T.

Local Lemma family_properties U i ρ ρ' B B' R S :
  per R -> lower_equiv U U i i ->
  (forall x y, R x y -> exists b b', Ev B ρ x b /\ Ev B' ρ' y b') ->
  (forall x y b b', R x y -> Ev B ρ x b -> Ev B' ρ' y b' ->
      ty U i b b' (S x y)) ->
  (forall x y b b', R x y -> Ev B ρ x b -> Ev B' ρ' y b' ->
      per (S x y) /\ coherent U i b b' (S x y)) ->
  family_per R S.
Proof.
  intros HR EI Ex Ct IH; split.
  - intros x y H; destruct (Ex _ _ H) as (b & b' & E & E').
    exact (proj1 (IH _ _ _ _ H E E')).
  - intros x y u v H K L.
    destruct (Ex _ _ H) as (b & b' & E & E').
    destruct (Ex _ _ K) as (c & c' & F & F').
    eapply (proj2 (IH _ _ _ _ H E E')); [exact EI | | eauto].
    destruct L as [-> | ->]; same_eval; auto.
Qed.

Local Lemma equiv_refl R : R ≃ R.
Proof. intros x y; reflexivity. Qed.

Local Lemma lower_equiv_refl U i : lower_equiv U U i i.
Proof. intros k _ _; apply equiv_refl. Qed.

Local Ltac invert_shared :=
  match goal with
  | E : _ = _ \/ _ = _ |- _ =>
    destruct E as [E | E]; inversion E; clear E; subst
  end.

Local Ltac family_coherence Ex Ex' Hcoh Hcod Eli E :=
  intros x y Hxy;
  let Hy := fresh in
  pose proof (proj1 (E x y) Hxy) as Hy;
  let D := fresh in let D' := fresh in let F := fresh in let F' := fresh in
  let Q := fresh in
  destruct (Ex _ _ Hxy) as (? & ? & D & D');
  destruct (Ex' _ _ Hy) as (? & ? & F & F');
  pose proof (Hcod _ _ _ _ Hy F F') as Q;
  refine (proj2 (Hcoh _ _ _ _ Hxy D D') _ _ _ _ _ Eli _ Q);
  same_eval; first [left; reflexivity | right; reflexivity].

(* The relation is a PER. Sharing either type endpoint determines the
   relation up to pointwise equivalence, even across universe levels. *)
Local Lemma ty_properties U i a b R :
  lower_per U i -> ty U i a b R -> per R /\ coherent U i a b R.
Proof.
  intros LP H.
  induction H as
      [j R J E | R E | a b m n R N E
      | a a' ρ ρ' B B' R S T HA [PR CA] Ex Cod IC E
      | a a' ρ ρ' B B' R S T HA [PR CA] Ex Cod IC E
      | a a' l l' r r' R T HA [PR CA] Hl Hr E];
    split.
  - eapply equiv_per; eauto.
  - intros V k c d S LE HE HS. inversion HS; subst; invert_shared.
    all: (eapply equiv_trans; [exact E |];
          eapply equiv_trans; [eapply LE; eassumption | intros x y; symmetry; auto]).
  - eapply equiv_per; eauto using nat_per.
  - intros V k c d S LE HE HS. inversion HS; subst; invert_shared.
    all: (eapply equiv_trans; [exact E | intros x y; symmetry; auto]).
  - eapply equiv_per; eauto using neutral_at_per.
  - intros V k c d S LE HE HS. inversion HS; subst; invert_shared.
    all: (eapply equiv_trans; [exact E | intros x y; symmetry; auto]).
  - eapply equiv_per; [exact E | apply pi_per; [exact PR |]].
    eapply family_properties; eauto using lower_equiv_refl.
  - intros V k c d T' LE HE HS. inversion HS; subst; invert_shared.
    all: (eapply equiv_trans; [exact E |];
          eapply equiv_trans; [apply pi_equiv | intros x y; symmetry; eauto]).
    all: match goal with
         | HS' : ty ?V ?k _ _ ?R', F : (forall x y, ?R' x y -> exists b b', _),
           G : (forall x y b b', ?R' x y -> _ -> _ -> ty ?V ?k b b' _) |- _ =>
           let DE := fresh in
           assert (DE : R ≃ R') by (refine (CA _ _ _ _ _ LE _ HS'); auto);
           first [exact DE | family_coherence Ex F IC G LE DE]
         end.
  - eapply equiv_per; [exact E | apply sigma_per; [exact PR |]].
    eapply family_properties; eauto using lower_equiv_refl.
  - intros V k c d T' LE HE HS. inversion HS; subst; invert_shared.
    all: (eapply equiv_trans; [exact E |];
          eapply equiv_trans; [apply sigma_equiv | intros x y; symmetry; eauto]).
    all: match goal with
         | HS' : ty ?V ?k _ _ ?R', F : (forall x y, ?R' x y -> exists b b', _),
           G : (forall x y b b', ?R' x y -> _ -> _ -> ty ?V ?k b b' _) |- _ =>
           let DE := fresh in
           assert (DE : R ≃ R') by (refine (CA _ _ _ _ _ LE _ HS'); auto);
           first [exact DE | family_coherence Ex F IC G LE DE]
         end.
  - eapply equiv_per; eauto using eq_per.
  - intros V k c d T' LE HE HS. inversion HS; subst; invert_shared.
    all: (eapply equiv_trans; [exact E |];
          eapply equiv_trans; [apply eq_equiv | intros x y; symmetry; eauto]).
    all: match goal with
         | HS' : ty ?V ?k _ _ ?R' |- _ =>
           let DE := fresh in
           assert (DE : R ≃ R') by (refine (CA _ _ _ _ _ LE _ HS'); auto);
           first [exact DE | solve [intro; apply DE] |
             apply endpoint_equiv; [exact PR | exact DE |];
             destruct PR as [Sym Tr];
             eapply Tr; [eassumption | apply Sym; apply DE; eassumption]]
         end.
Qed.

Local Lemma ty_per U i a b R :
  lower_per U i -> ty U i a b R -> per R.
Proof. intros LP H; exact (proj1 (ty_properties _ _ _ _ _ LP H)). Qed.

Local Lemma ty_coherence U V i j a b c d R T :
  lower_per U i -> lower_equiv U V i j ->
  ty U i a b R -> ty V j c d T -> a = c \/ b = d -> R ≃ T.
Proof. intros LP LE H K E; exact (proj2 (ty_properties _ _ _ _ _ LP H) _ _ _ _ _ LE E K). Qed.

Local Lemma ty_sym U i a b R : lower_per U i ->
  ty U i a b R -> ty U i b a R.
Proof.
  intros LP H.
  induction H as
      [j R J E | R E | a b m n R N E
      | a a' ρ ρ' B B' R S T HA IH Ex Cod IC E
      | a a' ρ ρ' B B' R S T HA IH Ex Cod IC E
      | a a' l l' r r' R T HA IH Hl Hr E];
    try solve [constructor; auto; apply neutral_per; assumption].
  all: assert (PR : per R) by (eapply ty_per; eassumption).
  - eapply ty_pi with (S := fun x y => S y x); [exact IH | | |].
    + intros x y H; assert (K : R y x) by (apply PR; exact H).
      destruct (Ex _ _ K) as (b & b' & ? & ?); eauto.
    + intros x y b b' H F G; apply IC; [apply PR | |]; assumption.
    + eapply equiv_trans; [exact E | apply pi_equiv; [apply equiv_refl |]].
      refine (family_swap R S PR _).
      eapply family_properties; eauto using lower_equiv_refl, ty_properties.
  - eapply ty_sigma with (S := fun x y => S y x); [exact IH | | |].
    + intros x y H; assert (K : R y x) by (apply PR; exact H).
      destruct (Ex _ _ K) as (b & b' & ? & ?); eauto.
    + intros x y b b' H F G; apply IC; [apply PR | |]; assumption.
    + eapply equiv_trans; [exact E | apply sigma_equiv; [apply equiv_refl |]].
      refine (family_swap R S PR _).
      eapply family_properties; eauto using lower_equiv_refl, ty_properties.
  - eapply ty_eq; [exact IH | apply PR; exact Hl | apply PR; exact Hr |].
    eapply equiv_trans; [exact E | apply eq_equiv; try apply endpoint_equiv;
      auto using equiv_refl].
Qed.

Local Lemma ty_join U i a b R : lower_per U i ->
  ty U i a b R -> forall c T, ty U i c b T -> ty U i a c R.
Proof.
  intros LP H.
  induction H as
      [j R J E | R E | a b m n R N E
      | a a' ρ ρ' B B' R S T HA IH Ex Cod IC E
      | a a' ρ ρ' B B' R S T HA IH Ex Cod IC E
      | a a' l l' r r' R T HA IH Hl Hr E];
    intros c Q K; inversion K; subst.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; [|assumption].
    destruct neutral_per as [Sym Tr]; eauto.
  - assert (LE : R ≃ R0) by
      (eapply ty_coherence; [exact LP | apply lower_equiv_refl | exact HA | exact H2 | auto]).
    assert (PR : per R) by (eapply ty_per; eassumption).
    eapply ty_pi with (S := S); [apply IH with (T := R0); exact H2 | | | exact E].
    + intros x y H; destruct (Ex _ _ H) as (b & b' & F & G).
      assert (Hyy : R0 y y) by (apply LE; eapply per_right; eassumption).
      destruct (H4 _ _ Hyy) as (c & c' & F' & G'); eauto.
    + intros x y b c H F G.
      assert (Hyy : R0 y y) by (apply LE; eapply per_right; eassumption).
      destruct (Ex _ _ H) as (b0 & b' & F0 & F').
      eapply (IC _ _ _ _ H F F'); eapply H6; eassumption.
  - assert (LE : R ≃ R0) by
      (eapply ty_coherence; [exact LP | apply lower_equiv_refl | exact HA | exact H2 | auto]).
    assert (PR : per R) by (eapply ty_per; eassumption).
    eapply ty_sigma with (S := S); [apply IH with (T := R0); exact H2 | | | exact E].
    + intros x y H; destruct (Ex _ _ H) as (b & b' & F & G).
      assert (Hyy : R0 y y) by (apply LE; eapply per_right; eassumption).
      destruct (H4 _ _ Hyy) as (c & c' & F' & G'); eauto.
    + intros x y b c H F G.
      assert (Hyy : R0 y y) by (apply LE; eapply per_right; eassumption).
      destruct (Ex _ _ H) as (b0 & b' & F0 & F').
      eapply (IC _ _ _ _ H F F'); eapply H6; eassumption.
  - assert (LE : R ≃ R0) by
      (eapply ty_coherence; [exact LP | apply lower_equiv_refl | exact HA | exact H2 | auto]).
    pose proof (ty_per _ _ _ _ _ LP HA) as [Sym Tr].
    eapply ty_eq; [exact (IH _ _ H2) | | | exact E].
    + eapply Tr; [exact Hl | apply Sym, LE, H4].
    + eapply Tr; [exact Hr | apply Sym, LE, H6].
Qed.

Local Lemma ty_lift U V i j a b R :
  i <= j -> lower_equiv U V i j -> ty U i a b R -> ty V j a b R.
Proof.
  intros Le E H; induction H; econstructor; eauto.
  - lia.
  - eapply equiv_trans; [eassumption | apply E; lia].
Qed.

Local Definition types_at U i : drel := fun a b => exists R, ty U i a b R.

Local Lemma types_at_per U i : lower_per U i -> per (types_at U i).
Proof.
  intros LP; split.
  - intros a b [R H]; exists R; eapply ty_sym; eassumption.
  - intros a b c [R H] [T K]; exists R; eapply ty_join;
      [exact LP | exact H | eapply ty_sym; eassumption].
Qed.

(* Each level interprets universe elements using the preceding levels. *)
Local Fixpoint tower (n : nat) : list drel :=
  match n with
  | O => nil
  | S k => tower k ++ (types_at (fun j => nth j (tower k) (fun _ _ => False)) k :: nil)
  end.
Local Definition levels i j : drel := nth j (tower i) (fun _ _ => False).
Local Definition sem_ty i := ty (levels i) i.
Local Definition any_ty a b R := exists i, sem_ty i a b R.

Local Lemma tower_length i : length (tower i) = i.
Proof. induction i; simpl; auto; rewrite length_app, IHi; simpl; lia. Qed.

Local Lemma levels_step i j : j < i -> levels (S i) j = levels i j.
Proof.
  unfold levels; simpl; intro L; apply app_nth1; now rewrite tower_length.
Qed.

Local Lemma levels_stable i j k : i <= j -> k < i -> levels j k = levels i k.
Proof.
  intros H K; induction H; auto.
  rewrite levels_step; auto; lia.
Qed.

Local Lemma levels_entry i : levels (S i) i = types_at (levels i) i.
Proof.
  unfold levels at 1; simpl.
  replace i with (length (tower i)) at 1 by apply tower_length.
  rewrite app_nth2 by lia. now rewrite Nat.sub_diag.
Qed.

Local Lemma level_unfold i k : k < i -> levels i k = types_at (levels k) k.
Proof.
  intro L. rewrite (levels_stable (S k) i k), levels_entry; auto.
Qed.

Local Lemma levels_per i : lower_per (levels i) i.
Proof.
  induction i as [i IH] using lt_wf_ind.
  intros j J; rewrite level_unfold by assumption; apply types_at_per, IH; assumption.
Qed.

Local Lemma levels_equiv i j : lower_equiv (levels i) (levels j) i j.
Proof.
  intros k Ki Kj; rewrite (level_unfold i k Ki), (level_unfold j k Kj); apply equiv_refl.
Qed.

Local Lemma sem_lift i j a b R : i <= j -> sem_ty i a b R -> sem_ty j a b R.
Proof. intros; eapply ty_lift; eauto using levels_equiv. Qed.

Local Lemma sem_per a b R : any_ty a b R -> per R.
Proof. intros [i H]; eapply ty_per; [apply levels_per | exact H]. Qed.

Local Lemma sem_coh a b c d R S :
  any_ty a b R -> any_ty c d S -> a = c \/ b = d -> R ≃ S.
Proof.
  intros [i H] [j K] E; eapply ty_coherence;
    [apply levels_per | apply levels_equiv | exact H | exact K | exact E].
Qed.

Local Lemma sem_sym a b R : any_ty a b R -> any_ty b a R.
Proof. intros [i H]; exists i; apply ty_sym; auto using levels_per. Qed.

Local Lemma sem_sol a b R : any_ty a b R -> any_ty a a R.
Proof.
  intros [i H]; exists i; eapply ty_join; [apply levels_per | exact H | exact H].
Qed.

Local Definition universe i : drel := types_at (levels i) i.

Local Lemma sem_univ i j : i < j -> sem_ty j (d_univ i) (d_univ i) (universe i).
Proof.
  intro L; constructor; [exact L | rewrite level_unfold by exact L; apply equiv_refl].
Qed.

Local Lemma any_univ i : any_ty (d_univ i) (d_univ i) (universe i).
Proof. exists (S i); apply sem_univ; lia. Qed.

Local Lemma any_nat : any_ty d_nat d_nat nat_rel.
Proof. exists 0; constructor; apply equiv_refl. Qed.

(* Reification gives common readbacks, and reflection supplies related
   neutral elements for readback underneath binders. *)
Local Definition quote_type a b :=
  forall s, exists W, read_typ s a W /\ read_typ s b W.
Local Definition quote_nf a b m n :=
  forall s, exists W, read_nf s (d_dom a m) W /\ read_nf s (d_dom b n) W.
Local Definition reflect a b (R : drel) :=
  forall m n, neutral m n -> R (d_neut a m) (d_neut b n).
Local Definition quote_reflect a b R :=
  quote_type a b /\ (forall m n, R m n -> quote_nf a b m n) /\ reflect a b R.

Local Lemma neutral_var s : neutral (d_var s) (d_var s).
Proof. intro k; eexists; split; constructor. Qed.

Local Lemma neutral_app a b m n x y :
  neutral m n -> quote_nf a b x y ->
  neutral (d_app m (d_dom a x)) (d_app n (d_dom b y)).
Proof.
  intros H Q s; destruct (H s) as (W & ? & ?), (Q s) as (V & ? & ?).
  eexists; split; eauto with mctt.
Qed.

Local Lemma neutral_fst m n : neutral m n -> neutral (d_fst m) (d_fst n).
Proof. intros H s; destruct (H s) as (W & ? & ?); eexists; split; eauto with mctt. Qed.
Local Lemma neutral_snd m n : neutral m n -> neutral (d_snd m) (d_snd n).
Proof. intros H s; destruct (H s) as (W & ? & ?); eexists; split; eauto with mctt. Qed.

Local Lemma nat_quote m n : nat_rel m n -> quote_nf d_nat d_nat m n.
Proof.
  induction 1; intro k.
  - eexists; split; constructor.
  - destruct (IHnat_rel k) as (W & ? & ?); eexists; split; eauto with mctt.
  - destruct (H k) as (W & ? & ?); eexists; split; eauto with mctt.
Qed.

Local Ltac quote_exists := eexists; split; solve [eauto 6 with mctt].

Local Lemma ty_quote U i a b R :
  (forall j, j < i -> forall m n, U j m n -> quote_type m n) ->
  (forall j, j < i -> reflect (d_univ j) (d_univ j) (U j)) ->
  ty U i a b R -> quote_reflect a b R.
Proof.
  intros LQ LR H.
  induction H as
      [j R J E | R E | a b m n R N E
      | a a' ρ ρ' B B' R S T HA [QA [QN RN]] Ex Cod IC E
      | a a' ρ ρ' B B' R S T HA [QA [QN RN]] Ex Cod IC E
      | a a' l l' r r' R T HA [QA [QN RN]] Hl Hr E];
    (split; [| split]).
  - intro s; quote_exists.
  - intros m n H s; apply E in H.
    destruct (LQ _ J _ _ H s) as (W & ? & ?); quote_exists.
  - intros m n H; apply E; apply LR; assumption.
  - intro s; quote_exists.
  - intros m n H; apply nat_quote, E, H.
  - intros m n H; apply E; constructor; assumption.
  - intro s; destruct (N s) as (W & ? & ?); quote_exists.
  - intros x y H s; apply E in H.
    destruct H as (? & ? & ? & ? & -> & -> & K).
    destruct (K s) as (W & ? & ?); quote_exists.
  - intros x y H; apply E; unfold neutral_at; eauto 8.
  - intro s; destruct (QA s) as (A & ? & ?).
    pose proof (RN _ _ (neutral_var s)) as K.
    destruct (Ex _ _ K) as (b & b' & F & G).
    destruct (proj1 (IC _ _ _ _ K F G) (Datatypes.S s)) as (W & ? & ?).
    quote_exists.
  - intros m n H s; apply E in H.
    destruct (QA s) as (A & ? & ?).
    pose proof (RN _ _ (neutral_var s)) as K.
    destruct (Ex _ _ K) as (b & b' & F & G).
    destruct (H _ _ K) as (x & y & ? & ? & Hxy).
    destruct (proj1 (proj2 (IC _ _ _ _ K F G)) _ _ Hxy (Datatypes.S s)) as (W & ? & ?).
    quote_exists.
  - intros m n H; apply E; intros x y K.
    destruct (Ex _ _ K) as (b & b' & F & G).
    eexists; eexists; split; [econstructor; exact F |].
    split; [econstructor; exact G |].
    apply (proj2 (proj2 (IC _ _ _ _ K F G))).
    apply neutral_app; [exact H | apply QN; exact K].
  - intro s; destruct (QA s) as (A & ? & ?).
    pose proof (RN _ _ (neutral_var s)) as K.
    destruct (Ex _ _ K) as (b & b' & F & G).
    destruct (proj1 (IC _ _ _ _ K F G) (Datatypes.S s)) as (W & ? & ?).
    quote_exists.
  - intros m n H s; apply E in H.
    destruct H as (x & y & u & v & Fx & Fy & K & Fu & Fv & L).
    destruct (QA s) as (A & ? & ?).
    pose proof (RN _ _ (neutral_var s)) as K'.
    destruct (Ex _ _ K') as (c & c' & F' & G').
    destruct (proj1 (IC _ _ _ _ K' F' G') (Datatypes.S s)) as (W & ? & ?).
    destruct (Ex _ _ K) as (b & b' & F & G).
    destruct (QN _ _ K s) as (X & ? & ?).
    destruct (proj1 (proj2 (IC _ _ _ _ K F G)) _ _ L s) as (Y & ? & ?).
    quote_exists.
  - intros m n H; apply E.
    pose proof (RN _ _ (neutral_fst _ _ H)) as K.
    destruct (Ex _ _ K) as (b & b' & F & G).
    do 4 eexists; repeat split; try solve [eauto with mctt].
    apply (proj2 (proj2 (IC _ _ _ _ K F G))), neutral_snd, H.
  - intro s; destruct (QA s) as (A & ? & ?),
        (QN _ _ Hl s) as (L & ? & ?), (QN _ _ Hr s) as (W & ? & ?).
    quote_exists.
  - intros m n H s; apply E in H; destruct H as [m n H _ _ | a0 b0 m n N].
    + destruct (QA s) as (A & ? & ?), (QN _ _ H s) as (W & ? & ?).
      quote_exists.
    + destruct (N s) as (W & ? & ?); quote_exists.
  - intros m n H; apply E; constructor; assumption.
Qed.

Local Lemma universe_quote i : forall a b, universe i a b -> quote_type a b.
Proof.
  induction i as [i IH] using lt_wf_ind.
  intros a b [R H]; refine (proj1 (ty_quote _ _ _ _ _ _ _ H)).
  - intros j J; rewrite level_unfold by exact J; apply IH, J.
  - intros j J m n N; rewrite level_unfold by exact J.
    exists neutral_at; constructor; auto using equiv_refl.
Qed.

Local Lemma sem_quote a b R : any_ty a b R -> quote_reflect a b R.
Proof.
  intros [i H]; refine (ty_quote _ _ _ _ _ _ _ H).
  - intros j J; rewrite level_unfold by exact J; apply universe_quote.
  - intros j J m n N; rewrite level_unfold by exact J.
    exists neutral_at; constructor; auto using equiv_refl.
Qed.

Local Lemma at_coh i j a b c d R S :
  sem_ty i a b R -> sem_ty j c d S -> a = c \/ b = d -> R ≃ S.
Proof. intros H K E; exact (sem_coh _ _ _ _ _ _ (ex_intro _ i H) (ex_intro _ j K) E). Qed.

Local Lemma at_per i a b R : sem_ty i a b R -> per R.
Proof. intro H; exact (sem_per _ _ _ (ex_intro _ i H)). Qed.

Local Definition eval_rel (R : drel) ρ ξ M N :=
  exists m n, eval_exp M ρ m /\ eval_exp N ξ n /\ R m n.

Local Definition fib ρ ξ B C x y : drel := fun m n =>
  exists b c R, Ev B ρ x b /\ Ev C ξ y c /\ any_ty b c R /\ R m n.

Local Lemma fib_equiv i ρ ξ B C x y b c R :
  Ev B ρ x b -> Ev C ξ y c -> sem_ty i b c R ->
  R ≃ fib ρ ξ B C x y.
Proof.
  intros F G H m n; split.
  - intro K; exists b, c, R; repeat split; auto; now exists i.
  - intros (b' & c' & S & F' & G' & K & L).
    same_eval.
    assert (E : R ≃ S) by (eapply sem_coh; [exists i; exact H | exact K | auto]).
    apply E, L.
Qed.

Local Definition family_at i R ρ ξ B C :=
  forall x y, R x y -> eval_rel (universe i) (ρ ▻ x) (ξ ▻ y) B C.

Local Lemma family_at_ex i R ρ ξ B C :
  family_at i R ρ ξ B C ->
  forall x y, R x y -> exists b c, Ev B ρ x b /\ Ev C ξ y c.
Proof. intros Fam x y H; destruct (Fam _ _ H) as (b & c & ? & ? & ?); eauto. Qed.

Local Lemma family_at_ty i R ρ ξ B C :
  family_at i R ρ ξ B C ->
  forall x y b c, R x y -> Ev B ρ x b -> Ev C ξ y c ->
    sem_ty i b c (fib ρ ξ B C x y).
Proof.
  intros Fam x y b c H F G.
  destruct (Fam _ _ H) as (b' & c' & F' & G' & T & K); same_eval.
  eapply ty_change; [exact K | intros m n; symmetry; eapply fib_equiv; eassumption].
Qed.

Local Lemma at_pi i a a' ρ ξ B C R :
  sem_ty i a a' R -> family_at i R ρ ξ B C ->
  sem_ty i (d_pi a ρ B) (d_pi a' ξ C) (pi_rel R (fib ρ ξ B C)).
Proof.
  intros H F; eapply ty_pi with (R := R) (S := fib ρ ξ B C);
    [exact H | apply (family_at_ex _ _ _ _ _ _ F) |
     exact (family_at_ty _ _ _ _ _ _ F) | apply equiv_refl].
Qed.

Local Lemma at_sigma i a a' ρ ξ B C R :
  sem_ty i a a' R -> family_at i R ρ ξ B C ->
  sem_ty i (d_sigma a ρ B) (d_sigma a' ξ C) (sigma_rel R (fib ρ ξ B C)).
Proof.
  intros H F; eapply ty_sigma with (R := R) (S := fib ρ ξ B C);
    [exact H | apply (family_at_ex _ _ _ _ _ _ F) |
     exact (family_at_ty _ _ _ _ _ _ F) | apply equiv_refl].
Qed.

Local Lemma at_eq i a a' x x' y y' R :
  sem_ty i a a' R -> R x x' -> R y y' ->
  sem_ty i (d_eq a x y) (d_eq a' x' y') (eq_rel R x y).
Proof. intros; econstructor; eauto using equiv_refl. Qed.

(* Contexts relate environments one entry at a time. *)
Local Fixpoint env_rel (Γ : ctx) (ρ ξ : env) : Prop :=
  match Γ with
  | nil => True
  | A :: Δ =>
      env_rel Δ (drop_env ρ) (drop_env ξ) /\
      exists a b R, eval_exp A (drop_env ρ) a /\ eval_exp A (drop_env ξ) b /\
          any_ty a b R /\ R (ρ 0) (ξ 0)
  end.

Local Lemma env_cons Γ A ρ ξ x y a b R :
  env_rel Γ ρ ξ -> eval_exp A ρ a -> eval_exp A ξ b -> any_ty a b R ->
  R x y -> env_rel (A :: Γ) (ρ ▻ x) (ξ ▻ y).
Proof. simpl; eauto 10. Qed.

Local Lemma env_cons_at i Γ A ρ ξ x y a b R :
  env_rel Γ ρ ξ -> eval_exp A ρ a -> eval_exp A ξ b -> sem_ty i a b R ->
  R x y -> env_rel (A :: Γ) (ρ ▻ x) (ξ ▻ y).
Proof. intros; eapply env_cons; eauto; now exists i. Qed.

Local Lemma env_nat Γ ρ ξ x y :
  env_rel Γ ρ ξ -> nat_rel x y ->
  env_rel (a_nat :: Γ) (ρ ▻ x) (ξ ▻ y).
Proof. intros; eapply env_cons; eauto using any_nat with mctt. Qed.

Local Lemma env_sym Γ ρ ξ : env_rel Γ ρ ξ -> env_rel Γ ξ ρ.
Proof.
  revert ρ ξ; induction Γ as [| A Γ IH]; intros ρ ξ H; [exact I |].
  destruct H as (H & a & b & R & F & G & K & L).
  simpl; split; [auto |].
  exists b, a, R; repeat split; auto using sem_sym.
  apply (sem_per _ _ _ K); assumption.
Qed.

Local Lemma env_trans Γ ρ ξ ζ :
  env_rel Γ ρ ξ -> env_rel Γ ξ ζ -> env_rel Γ ρ ζ.
Proof.
  revert ρ ξ ζ; induction Γ as [| A Γ IH]; intros ρ ξ ζ H K; [exact I |].
  destruct H as (H & a & b & R & F & G & HR & L).
  destruct K as (K & b' & c & S & G' & I' & HS & L').
  same_eval.
  pose proof (sem_coh _ _ _ _ _ _ (sem_sym _ _ _ HR) HS (or_introl eq_refl)) as E.
  split; [eauto |].
  destruct HR as [i HR]; destruct HS as [j HS].
  exists a, c, R; repeat split; auto.
  - exists (Nat.max i j).
    eapply ty_join; [apply levels_per | eapply sem_lift; [apply Nat.le_max_l | exact HR] |].
    eapply sem_lift; [apply Nat.le_max_r | apply ty_sym; [apply levels_per | exact HS]].
  - eapply (proj2 (at_per _ _ _ _ HR)); [exact L | apply E; exact L'].
Qed.

Local Lemma env_left Γ ρ ξ : env_rel Γ ρ ξ -> env_rel Γ ρ ρ.
Proof. intro H; eapply env_trans; [exact H | apply env_sym, H]. Qed.

(* The universe bound for a term's type is uniform over environments. *)
Local Definition sem_exp Γ A M N :=
  exists i, forall ρ ξ, env_rel Γ ρ ξ ->
    exists a b R, eval_exp A ρ a /\ eval_exp A ξ b /\
      sem_ty i a b R /\ eval_rel R ρ ξ M N.

Local Lemma sem_exp_type Γ i M N :
  sem_exp Γ (a_typ i) M N <->
  forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ M N.
Proof.
  split.
  - intros [j H] ρ ξ K.
    destruct (H _ _ K) as (a & b & R & F & G & T & x & y & Fx & Fy & L).
    inversion F; inversion G; subst.
    pose proof (at_coh _ _ _ _ _ _ _ _ T (sem_univ i (S i) (Nat.lt_succ_diag_r i))
      (or_introl eq_refl)) as E.
    exists x, y; repeat split; auto. apply E; assumption.
  - intros H; exists (S i); intros ρ ξ K.
    exists (d_univ i), (d_univ i), (universe i); repeat split; eauto with mctt.
    apply sem_univ; lia.
Qed.

Local Lemma sem_exp_nat Γ M N :
  sem_exp Γ a_nat M N <->
  forall ρ ξ, env_rel Γ ρ ξ -> eval_rel nat_rel ρ ξ M N.
Proof.
  split.
  - intros [j H] ρ ξ K.
    destruct (H _ _ K) as (a & b & R & F & G & T & x & y & Fx & Fy & L).
    inversion F; inversion G; subst. inversion T; subst.
    exists x, y; repeat split; auto. match goal with E : _ ≃ nat_rel |- _ => apply E; assumption end.
  - intros H; exists 0; intros ρ ξ K.
    exists d_nat, d_nat, nat_rel; repeat split; eauto with mctt.
    constructor; apply equiv_refl.
Qed.

Local Definition sem_sub Γ Δ σ τ :=
  forall ρ ξ, env_rel Γ ρ ξ ->
    exists η θ, eval_sub σ ρ η /\ eval_sub τ ξ θ /\ env_rel Δ η θ.
Local Definition sem_ctx_sub Γ Δ := forall ρ ξ, env_rel Γ ρ ξ -> env_rel Δ ρ ξ.

Local Definition sub_values a b :=
  exists R S, any_ty a a R /\ any_ty b b S /\ incl R S.
Local Definition sem_subtyp Γ A B :=
  forall ρ, env_rel Γ ρ ρ ->
    exists a b, eval_exp A ρ a /\ eval_exp B ρ b /\ sub_values a b.

Local Lemma sub_values_incl a a' b b' R S :
  sub_values a b -> any_ty a a' R -> any_ty b b' S -> incl R S.
Proof.
  intros (T & U & HT & HU & K) HR HS x y L.
  assert (E : R ≃ T) by (eapply sem_coh; eauto).
  assert (F : S ≃ U) by (eapply sem_coh; eauto).
  apply F, K, E, L.
Qed.

Inductive valid_ctx : ctx -> Prop :=
| valid_empty : valid_ctx nil
| valid_extend Γ A i : valid_ctx Γ ->
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  valid_ctx (A :: Γ).

Local Lemma valid_initial Γ : valid_ctx Γ ->
  exists ρ, initial_env Γ ρ /\ env_rel Γ ρ ρ.
Proof.
  induction 1 as [| Γ A i H [ρ [HI HR]] HA].
  - exists empty_env; split; [constructor | exact I].
  - destruct (HA _ _ HR) as (a & b & F & G & R & K); same_eval.
    pose proof (sem_quote _ _ _ (ex_intro _ i K)) as [_ [_ Ref]].
    exists (ρ ▻ d_neut a (d_var (length Γ))); split.
    + constructor; assumption.
    + eapply env_cons_at; eauto using neutral_var.
Qed.

Local Lemma lookup_sem Γ x A : ctx_lookup x A Γ ->
  valid_ctx Γ -> sem_exp Γ A (a_var x) (a_var x).
Proof.
  induction 1 as [A Γ | n A Γ B H IH]; intro V; inversion V; subst.
  - exists i; intros ρ ξ (H & a & b & R & F & G & T & L).
    destruct (H2 _ _ H) as (a' & b' & F' & G' & S & K); same_eval.
    exists a, b, S; repeat split; eauto with mctt.
    exists (ρ 0), (ξ 0); repeat split; eauto with mctt.
    assert (E : S ≃ R) by (eapply sem_coh; [exists i; exact K | exact T | auto]).
    apply E, L.
  - destruct (IH ltac:(assumption)) as [i0 K].
    exists i0; intros ρ ξ [HR _].
    destruct (K _ _ HR) as (a & b & R & F & G & T & m & n' & Fx & Fy & L).
    inversion Fx; inversion Fy; subst.
    exists a, b, R; repeat split; eauto with mctt.
    exists (ρ (S n)), (ξ (S n)); repeat split; eauto with mctt.
Qed.

Local Lemma eval_q σ ρ ξ x :
  eval_sub σ ρ ξ -> eval_sub (Syntax.q σ) (ρ ▻ x) (ξ ▻ x).
Proof.
  intro H. constructor; [eapply eval_sub_compose; [constructor | exact H] | constructor].
Qed.

Local Hint Resolve eval_q : mctt.

Local Lemma sub_unique σ ρ ξ η :
  eval_sub σ ρ ξ -> eval_sub σ ρ η -> ξ = η.
Proof.
  exact (fun H => (proj2 (proj2 (proj2 (proj2 (proj2 evaluation_unique))))) σ ρ ξ H η).
Qed.

Local Lemma at_sym i a b R : sem_ty i a b R -> sem_ty i b a R.
Proof. apply ty_sym, levels_per. Qed.

Local Lemma sem_exp_sym Γ A M N : sem_exp Γ A M N -> sem_exp Γ A N M.
Proof.
  intros [i H]; exists i; intros ρ ξ L.
  destruct (H _ _ (env_sym _ _ _ L)) as (b & a & R & G & F & T & y & x & Fy & Fx & L').
  exists a, b, R; repeat split; auto using at_sym.
  exists x, y; repeat split; auto. apply (at_per _ _ _ _ T); assumption.
Qed.

Local Lemma sem_exp_trans Γ A M N P :
  sem_exp Γ A M N -> sem_exp Γ A N P -> sem_exp Γ A M P.
Proof.
  intros [i H] [j K]; exists (Nat.max i j); intros ρ ξ L.
  destruct (H _ _ L) as (a & b & R & F & G & HR & x & y & Fx & Fy & L').
  assert (Lξ : env_rel Γ ξ ξ) by (eapply env_left; apply env_sym, L).
  destruct (K _ _ Lξ) as (b' & c & S & G' & I' & HS & y' & z & Fy' & Fz & L'').
  same_eval.
  assert (E : R ≃ S) by (eapply at_coh; [exact HR | exact HS | auto]).
  exists a, b, R; repeat split; auto.
  - eapply sem_lift; [apply Nat.le_max_l | exact HR].
  - exists x, z; repeat split; auto.
    eapply (proj2 (at_per _ _ _ _ HR)); [exact L' | apply E; exact L''].
Qed.

Local Lemma sem_exp_left Γ A M N : sem_exp Γ A M N -> sem_exp Γ A M M.
Proof. intro H; eapply sem_exp_trans; [exact H | apply sem_exp_sym, H]. Qed.

Local Lemma sem_sub_sym Γ Δ σ τ : sem_sub Γ Δ σ τ -> sem_sub Γ Δ τ σ.
Proof.
  intros H ρ ξ L.
  destruct (H _ _ (env_sym _ _ _ L)) as (η & θ & F & G & K).
  exists θ, η; auto using env_sym.
Qed.

Local Lemma sem_sub_trans Γ Δ σ τ υ :
  sem_sub Γ Δ σ τ -> sem_sub Γ Δ τ υ -> sem_sub Γ Δ σ υ.
Proof.
  intros H K ρ ξ L.
  destruct (H _ _ L) as (η & θ & F & G & K').
  assert (Lξ : env_rel Γ ξ ξ) by (eapply env_left; apply env_sym, L).
  destruct (K _ _ Lξ) as (θ' & ζ & G' & I' & L').
  pose proof (sub_unique _ _ _ _ G G') as E; subst θ'.
  exists η, ζ; repeat split; eauto using env_trans.
Qed.

Local Lemma sem_sub_left Γ Δ σ τ : sem_sub Γ Δ σ τ -> sem_sub Γ Δ σ σ.
Proof. intro H; eapply sem_sub_trans; [exact H | apply sem_sub_sym, H]. Qed.

Local Lemma sem_exp_substitute Γ Δ A M N σ τ :
  sem_exp Δ A M N -> sem_sub Γ Δ σ τ ->
  sem_exp Γ (a_sub A σ) (a_sub M σ) (a_sub N τ).
Proof.
  intros [i HM] HS.
  pose proof (sem_sub_left _ _ _ _ HS) as HS0.
  exists i; intros ρ ξ H.
  destruct (HS _ _ H) as (η & θ & F & G & K).
  destruct (HS0 _ _ H) as (η' & θ' & F' & G' & K').
  pose proof (sub_unique _ _ _ _ F F') as E; subst η'.
  destruct (HM _ _ K) as (a & b & R & Fa & Fb & T & x & y & Fx & Fy & L).
  destruct (HM _ _ K') as (a' & b' & R' & Fa' & Fb' & T' & _).
  same_eval.
  exists a, b', R'; repeat split; eauto with mctt.
  exists x, y; repeat split; eauto with mctt.
  assert (E : R ≃ R') by (eapply at_coh; [exact T | exact T' | auto]).
  apply E, L.
Qed.

Local Definition eval_into ρ ξ M N :=
  forall m, eval_exp M ρ m -> eval_exp N ξ m.

Local Lemma exp_transport Γ A M N B P Q :
  sem_exp Γ A M N ->
  (forall ρ, eval_into ρ ρ A B) ->
  (forall ρ, eval_into ρ ρ M P) ->
  (forall ρ, eval_into ρ ρ N Q) ->
  sem_exp Γ B P Q.
Proof.
  intros [i H] HA HM HN; unfold eval_into in *; exists i; intros ρ ξ K.
  destruct (H _ _ K) as (a & b & R & F & G & T & m & n & L & O & Hmn).
  exists a, b, R; repeat split; auto.
  exists m, n; repeat split; auto.
Qed.

Local Lemma into_refl ρ M : eval_into ρ ρ M M.
Proof. unfold eval_into; auto. Qed.
Local Hint Resolve into_refl : mctt.

Local Lemma into_sub_id ρ M : eval_into ρ ρ M (a_sub M a_id).
Proof. unfold eval_into; eauto with mctt. Qed.
Local Hint Resolve into_sub_id : mctt.

Local Lemma into_sub_compose ρ M σ τ :
  eval_into ρ ρ (a_sub M (a_compose σ τ)) (a_sub (a_sub M σ) τ).
Proof.
  intros m H; inversion H; subst.
  match goal with K : eval_sub (a_compose _ _) _ _ |- _ => inversion K; subst end.
  eauto with mctt.
Qed.

Local Lemma subtyp_exp Γ A B M N i :
  sem_exp Γ A M N ->
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ B B) ->
  sem_subtyp Γ A B -> sem_exp Γ B M N.
Proof.
  intros [j H] K L; exists i; intros ρ ξ E.
  destruct (H _ _ E) as (a & a' & R & F & F' & T & x & y & Fx & Fy & Hxy).
  destruct (K _ _ E) as (b & b' & G & G' & S & U).
  destruct (L _ (env_left _ _ _ E)) as (a0 & b0 & F0 & G0 & V).
  same_eval.
  exists b, b', S; repeat split; auto.
  exists x, y; repeat split; auto.
  exact (sub_values_incl _ _ _ _ _ _ V (ex_intro _ j T) (ex_intro _ i U) _ _ Hxy).
Qed.

Local Lemma subtyp_refl Γ A B i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A B) ->
  sem_subtyp Γ A B.
Proof.
  intros H ρ E.
  destruct (H _ _ E) as (a & b & F & G & R & T).
  exists a, b; repeat split; auto.
  exists R, R; repeat split.
  - exact (sem_sol _ _ _ (ex_intro _ i T)).
  - exact (sem_sol _ _ _ (sem_sym _ _ _ (ex_intro _ i T))).
  - unfold incl; auto.
Qed.

Local Lemma subtyp_trans Γ A B C :
  sem_subtyp Γ A B -> sem_subtyp Γ B C -> sem_subtyp Γ A C.
Proof.
  intros H K ρ E.
  destruct (H _ E) as (a & b & F & G & R & S & HR & HS & L).
  destruct (K _ E) as (b' & c & G' & I' & T & U & HT & HU & L').
  same_eval.
  exists a, c; repeat split; auto.
  exists R, U; repeat split; auto.
  intros x y Lxy; apply L'.
  assert (Coh : S ≃ T) by (eapply sem_coh; eauto).
  apply Coh, L, Lxy.
Qed.

Local Lemma subtyp_univ Γ i j : i < j -> sem_subtyp Γ (a_typ i) (a_typ j).
Proof.
  intros L ρ H.
  exists (d_univ i), (d_univ j); repeat split; try constructor.
  exists (universe i), (universe j); split; [apply any_univ | split; [apply any_univ |]].
  intros x y [R K]; exists R; eapply sem_lift; [apply Nat.lt_le_incl; exact L | exact K].
Qed.

Local Lemma ctx_sub_extend Γ Δ A B i :
  sem_ctx_sub Γ Δ ->
  (forall ρ ξ, env_rel Δ ρ ξ -> eval_rel (universe i) ρ ξ B B) ->
  sem_subtyp Γ A B -> sem_ctx_sub (A :: Γ) (B :: Δ).
Proof.
  intros H HB K ρ ξ (L & a & a' & R & F & G & T & N).
  specialize (H _ _ L).
  destruct (HB _ _ H) as (b & b' & F' & G' & S & U).
  destruct (K _ (env_left _ _ _ L)) as (a0 & b0 & F0 & G0 & V); same_eval.
  split; [exact H |].
  exists b, b', S; repeat split; auto.
  - now exists i.
  - exact (sub_values_incl _ _ _ _ _ _ V T (ex_intro _ i U) _ _ N).
Qed.

Local Lemma eval_sub_exp_inv M σ ρ m :
  eval_exp (a_sub M σ) ρ m -> exists ξ, eval_sub σ ρ ξ /\ eval_exp M ξ m.
Proof. inversion 1; subst; eauto. Qed.

Local Lemma sub_extend Γ Δ A i σ τ M N :
  sem_sub Γ Δ σ τ ->
  (forall ρ ξ, env_rel Δ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  sem_exp Γ (a_sub A σ) M N ->
  sem_sub Γ (A :: Δ) (a_extend σ M) (a_extend τ N).
Proof.
  intros HS HA [j HM] ρ ξ H.
  destruct (HS _ _ H) as (η & θ & F & G & K).
  destruct (HA _ _ K) as (a & b & L & O & R & T).
  destruct (HM _ _ H) as (a' & b' & S & L' & O' & U & x & y & Fx & Fy & K').
  destruct (eval_sub_exp_inv _ _ _ _ L') as (η' & F' & L'').
  pose proof (sub_unique _ _ _ _ F F') as EE; subst η'.
  same_eval.
  assert (E : S ≃ R) by (eapply at_coh; [exact U | exact T | auto]).
  exists (η ▻ x), (θ ▻ y); repeat split; eauto with mctt.
  exists a, b, R; repeat split; auto.
  - now exists i.
  - apply E, K'.
Qed.

Local Lemma sub_compose Γ Δ Ξ σ σ' τ τ' :
  sem_sub Γ Δ τ τ' -> sem_sub Δ Ξ σ σ' ->
  sem_sub Γ Ξ (a_compose σ τ) (a_compose σ' τ').
Proof.
  intros HT HS ρ ξ H.
  destruct (HT _ _ H) as (η & θ & F & G & K).
  destruct (HS _ _ K) as (η' & θ' & F' & G' & K').
  exists η', θ'; repeat split; eauto with mctt.
Qed.

Local Lemma terms_with Γ A M N ρ ξ a b R i :
  sem_exp Γ A M N -> env_rel Γ ρ ξ -> eval_exp A ρ a ->
  sem_ty i a b R -> eval_rel R ρ ξ M N.
Proof.
  intros [j H] E F T.
  destruct (H _ _ E) as (a' & b' & S & F' & G & U & m & n & L & O & K).
  same_eval.
  assert (C : S ≃ R) by (eapply at_coh; [exact U | exact T | auto]).
  exists m, n; repeat split; auto. apply C, K.
Qed.

Local Lemma family_from_ctx Γ A i ρ ξ a a' R B C :
  env_rel Γ ρ ξ -> eval_exp A ρ a -> eval_exp A ξ a' -> sem_ty i a a' R ->
  (forall ρ ξ, env_rel (A :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B C) ->
  family_at i R ρ ξ B C.
Proof.
  intros H F G T K x y L; apply K; eapply env_cons_at; eassumption.
Qed.

Local Lemma form_pi Γ A A' B B' i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A') ->
  (forall ρ ξ, env_rel (A :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B B') ->
  forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ (a_pi A B) (a_pi A' B').
Proof.
  intros HA HB ρ ξ H.
  destruct (HA _ _ H) as (a & b & F & G & R & T).
  assert (HAA : forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A).
  { apply sem_exp_type, (sem_exp_left Γ (a_typ i) A A'), sem_exp_type, HA. }
  destruct (HAA _ _ H) as (a0 & b0 & F0 & G0 & S & U); same_eval.
  assert (E : R ≃ S) by (eapply at_coh; [exact T | exact U | auto]).
  exists (d_pi a ρ B), (d_pi b ξ B'); repeat split; eauto with mctt.
  exists (pi_rel R (fib ρ ξ B B')); apply at_pi; [exact T |].
  intros x y K; apply HB; eapply env_cons_at; try eassumption; apply E, K.
Qed.

Local Lemma form_sigma Γ A A' B B' i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A') ->
  (forall ρ ξ, env_rel (A :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B B') ->
  forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ (a_sigma A B) (a_sigma A' B').
Proof.
  intros HA HB ρ ξ H.
  destruct (HA _ _ H) as (a & b & F & G & R & T).
  assert (HAA : forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A).
  { apply sem_exp_type, (sem_exp_left Γ (a_typ i) A A'), sem_exp_type, HA. }
  destruct (HAA _ _ H) as (a0 & b0 & F0 & G0 & S & U); same_eval.
  assert (E : R ≃ S) by (eapply at_coh; [exact T | exact U | auto]).
  exists (d_sigma a ρ B), (d_sigma b ξ B'); repeat split; eauto with mctt.
  exists (sigma_rel R (fib ρ ξ B B')); apply at_sigma; [exact T |].
  intros x y K; apply HB; eapply env_cons_at; try eassumption; apply E, K.
Qed.

Local Lemma form_eq Γ A A' M M' N N' i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A') ->
  sem_exp Γ A M M' -> sem_exp Γ A N N' ->
  forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ (a_eq A M N) (a_eq A' M' N').
Proof.
  intros HA HM HN ρ ξ E.
  destruct (HA _ _ E) as (a & b & F & G & R & T).
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HM E F T) as (x & y & Fx & Fy & K).
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HN E F T) as (u & v & Fu & Fv & L).
  exists (d_eq a x u), (d_eq b y v); repeat split; eauto with mctt.
  exists (eq_rel R x u); eapply at_eq; eassumption.
Qed.

Local Lemma term_fn Γ A A' B M M' i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  sem_exp (A :: Γ) B M M' ->
  sem_exp Γ (a_pi A B) (a_fn A M) (a_fn A' M').
Proof.
  intros HA [j HM]. exists (Nat.max i j); intros ρ ξ E.
  destruct (HA _ _ E) as (a & b & F & G & R & T).
  assert (HB : family_at (Nat.max i j) R ρ ξ B B).
  { intros x y K.
    assert (K' : env_rel (A :: Γ) (ρ ▻ x) (ξ ▻ y))
      by (eapply env_cons_at; eassumption).
    destruct (HM _ _ K') as (u & v & S & Fu & Fv & U & _).
    exists u, v; repeat split; auto.
    exists S; eapply sem_lift; [apply Nat.le_max_r | exact U]. }
  exists (d_pi a ρ B), (d_pi b ξ B), (pi_rel R (fib ρ ξ B B)); repeat split; eauto with mctt.
  - apply at_pi; [eapply sem_lift; [apply Nat.le_max_l | exact T] | exact HB].
  - exists (d_fn ρ M), (d_fn ξ M'); repeat split; eauto with mctt.
    intros x y K.
    assert (K' : env_rel (A :: Γ) (ρ ▻ x) (ξ ▻ y))
      by (eapply env_cons_at; eassumption).
    destruct (HM _ _ K') as (u & v & S & Fu & Fv & U & m & n & Fm & Fn & L).
    exists m, n; repeat split; eauto with mctt.
    exists u, v, S; repeat split; auto. now exists j.
Qed.

Local Lemma term_refl Γ A A' M M' i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  sem_exp Γ A M M' ->
  sem_exp Γ (a_eq A M M) (a_refl A M) (a_refl A' M').
Proof.
  intros HA HM.
  pose proof (sem_exp_left _ _ _ _ HM) as HM0.
  exists i; intros ρ ξ E.
  destruct (HA _ _ E) as (a & b & F & G & R & T).
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HM E F T) as (x & y & Fx & Fy & K).
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HM0 E F T) as (x0 & y0 & Fx0 & Fy0 & K0); same_eval.
  exists (d_eq a x x), (d_eq b y0 y0), (eq_rel R x x); repeat split; eauto with mctt.
  - eapply at_eq; eassumption.
  - exists (d_refl x), (d_refl y); repeat split; eauto with mctt.
    assert (Kx : R x x) by exact (per_left R (at_per _ _ _ _ T) _ _ K).
    apply eq_rel_refl; assumption.
Qed.

Local Lemma eval_at_id ρ M x :
  eval_exp M ρ x -> eval_sub (a_extend a_id M) ρ (ρ ▻ x).
Proof. constructor; auto with mctt. Qed.
Local Hint Resolve eval_at_id : mctt.

Local Lemma term_app Γ A B M M' N N' i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (A :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B B) ->
  sem_exp Γ (a_pi A B) M M' -> sem_exp Γ A N N' ->
  sem_exp Γ (a_sub B (a_extend a_id N)) (a_app M N) (a_app M' N').
Proof.
  intros HA HB HM HN; exists i; intros ρ ξ E.
  destruct (HA _ _ E) as (a & b & F & G & R & T).
  pose proof (family_from_ctx _ _ _ _ _ _ _ _ _ _ E F G T HB) as Fam.
  pose proof (at_pi _ _ _ _ _ _ _ _ T Fam) as TP.
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HM E (eval_exp_pi _ _ _ _ F) TP)
    as (f & g & Ff & Fg & K).
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HN E F T) as (x & y & Fx & Fy & L).
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ (sem_exp_left _ _ _ _ HN) E F T)
    as (x0 & y0 & Fx0 & Fy0 & L0); same_eval.
  destruct (K _ _ L) as (u & v & Fu & Fv & c & d & S' & Fc & Fd & U & Huv).
  destruct (Fam _ _ L0) as (c0 & d0 & Fc0 & Fd0 & S & V); same_eval.
  assert (C : S' ≃ S) by (eapply sem_coh; [exact U | exact (ex_intro _ i V) | auto]).
  exists c, d0, S; repeat split; eauto with mctt.
  exists u, v; repeat split; eauto with mctt. apply C, Huv.
Qed.

Local Lemma term_pair Γ A A' B B' M M' N N' i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (A :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B B) ->
  sem_exp Γ A M M' -> sem_exp Γ (a_sub B (a_extend a_id M)) N N' ->
  sem_exp Γ (a_sigma A B) (a_pair M A N B) (a_pair M' A' N' B').
Proof.
  intros HA HB HM HN; exists i; intros ρ ξ E.
  destruct (HA _ _ E) as (a & b & F & G & R & T).
  pose proof (family_from_ctx _ _ _ _ _ _ _ _ _ _ E F G T HB) as Fam.
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HM E F T) as (x & y & Fx & Fy & L).
  destruct (Fam _ _ L) as (c & d & Fc & Fd & S' & U).
  assert (Fsub : eval_exp (a_sub B (a_extend a_id M)) ρ c) by (eauto with mctt).
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HN E Fsub U) as (u & v & Fu & Fv & Huv).
  exists (d_sigma a ρ B), (d_sigma b ξ B), (sigma_rel R (fib ρ ξ B B));
    repeat split; eauto using at_sigma with mctt.
  exists (d_pair x u), (d_pair y v); repeat split; eauto with mctt.
  exists x, y, u, v; repeat split; eauto with mctt.
  exists c, d, S'; repeat split; auto. now exists i.
Qed.

Local Lemma term_fst Γ A B M M' i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (A :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B B) ->
  sem_exp Γ (a_sigma A B) M M' ->
  sem_exp Γ A (a_fst M) (a_fst M').
Proof.
  intros HA HB HM; exists i; intros ρ ξ E.
  destruct (HA _ _ E) as (a & b & F & G & R & T).
  pose proof (family_from_ctx _ _ _ _ _ _ _ _ _ _ E F G T HB) as Fam.
  pose proof (at_sigma _ _ _ _ _ _ _ _ T Fam) as TP.
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HM E (eval_exp_sigma _ _ _ _ F) TP)
    as (f & g & Ff & Fg & x & y & u & v & Fx & Fy & K & Fu & Fv & L).
  exists a, b, R; repeat split; auto.
  exists x, y; repeat split; eauto with mctt.
Qed.

Local Lemma term_snd Γ A B M M' i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (A :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B B) ->
  sem_exp Γ (a_sigma A B) M M' ->
  sem_exp Γ (a_sub B (a_extend a_id (a_fst M))) (a_snd M) (a_snd M').
Proof.
  intros HA HB HM; exists i; intros ρ ξ E.
  destruct (HA _ _ E) as (a & b & F & G & R & T).
  pose proof (family_from_ctx _ _ _ _ _ _ _ _ _ _ E F G T HB) as Fam.
  pose proof (at_sigma _ _ _ _ _ _ _ _ T Fam) as TP.
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HM E (eval_exp_sigma _ _ _ _ F) TP)
    as (f & g & Ff & Fg & x & y & u & v & Fx & Fy & K & Fu & Fv & c & d & S' & Fc & Fd & U & Huv).
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ (sem_exp_left _ _ _ _ HM) E (eval_exp_sigma _ _ _ _ F) TP)
    as (f0 & g0 & Ff0 & Fg0 & x0 & y0 & u0 & v0 & Fx0 & Fy0 & K0 & _); same_eval.
  destruct (Fam _ _ K0) as (c0 & d0 & Fc0 & Fd0 & S & V); same_eval.
  assert (C : S' ≃ S) by (eapply sem_coh; [exact U | exact (ex_intro _ i V) | auto]).
  exists c, d0, S; repeat split; eauto 7 with mctt.
  exists u, v; repeat split; eauto with mctt. apply C, Huv.
Qed.

Local Lemma pi_eta Γ A B M i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (A :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B B) ->
  sem_exp Γ (a_pi A B) M M ->
  sem_exp Γ (a_pi A B) M (a_fn A (a_app (a_sub M a_weaken) (a_var 0))).
Proof.
  intros HA HB HM; exists i; intros ρ ξ E.
  destruct (HA _ _ E) as (a & b & F & G & R & T).
  pose proof (family_from_ctx _ _ _ _ _ _ _ _ _ _ E F G T HB) as Fam.
  pose proof (at_pi _ _ _ _ _ _ _ _ T Fam) as TP.
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HM E (eval_exp_pi _ _ _ _ F) TP)
    as (f & g & Ff & Fg & K).
  exists (d_pi a ρ B), (d_pi b ξ B), (pi_rel R (fib ρ ξ B B)); repeat split; eauto with mctt.
  eexists f, (d_fn ξ _); repeat split; eauto with mctt.
  intros x y L; destruct (K _ _ L) as (u & v & Fu & Fv & L').
  exists u, v; repeat split; eauto 8 with mctt.
Qed.

Local Lemma sigma_eta Γ A B M i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (A :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B B) ->
  sem_exp Γ (a_sigma A B) M M ->
  sem_exp Γ (a_sigma A B) M (a_pair (a_fst M) A (a_snd M) B).
Proof.
  intros HA HB HM; exists i; intros ρ ξ E.
  destruct (HA _ _ E) as (a & b & F & G & R & T).
  pose proof (family_from_ctx _ _ _ _ _ _ _ _ _ _ E F G T HB) as Fam.
  pose proof (at_sigma _ _ _ _ _ _ _ _ T Fam) as TP.
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HM E (eval_exp_sigma _ _ _ _ F) TP)
    as (f & g & Ff & Fg & x & y & u & v & Fx & Fy & K & Fu & Fv & L).
  exists (d_sigma a ρ B), (d_sigma b ξ B), (sigma_rel R (fib ρ ξ B B)); repeat split; eauto with mctt.
  exists f, (d_pair y v); repeat split; eauto with mctt.
  exists x, y, u, v; repeat split; eauto with mctt.
Qed.

Local Lemma same_at i a b R : sem_ty i a b R -> sem_ty i a a R.
Proof. intro H; apply (ty_join _ _ _ _ _ (levels_per i) H _ _ H). Qed.

Local Lemma family_sub Γ A B C i ρ a R :
  env_rel Γ ρ ρ -> eval_exp A ρ a -> sem_ty i a a R ->
  family_at i R ρ ρ C C -> sem_subtyp (A :: Γ) B C ->
  forall x y, R x y -> incl (fib ρ ρ B B x y) (fib ρ ρ C C x y).
Proof.
  intros E F T FC HS x y K u v (b & b' & S & Fb & Fb' & U & L).
  assert (Kx : R x x) by exact (per_left R (at_per _ _ _ _ T) _ _ K).
  assert (Ex : env_rel (A :: Γ) (ρ ▻ x) (ρ ▻ x)) by (eapply env_cons_at; eassumption).
  destruct (HS _ Ex) as (b0 & c & Fb0 & Fc & V).
  destruct (FC _ _ K) as (c0 & c' & Fc0 & Fc' & S' & W); same_eval.
  exists c, c', S'; repeat split; auto.
  - now exists i.
  - exact (sub_values_incl _ _ _ _ _ _ V U (ex_intro _ i W) _ _ L).
Qed.

Local Lemma subtyp_pi Γ A A' B B' i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A') ->
  (forall ρ ξ, env_rel (A :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B B) ->
  (forall ρ ξ, env_rel (A' :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B' B') ->
  sem_subtyp (A' :: Γ) B B' -> sem_subtyp Γ (a_pi A B) (a_pi A' B').
Proof.
  intros HA HB HC HS ρ E.
  destruct (HA _ _ E) as (a & b & F & G & R & T).
  pose proof (same_at _ _ _ _ T) as TA.
  pose proof (same_at _ _ _ _ (at_sym _ _ _ _ T)) as TB.
  pose proof (family_from_ctx _ _ _ _ _ _ _ _ _ _ E F F TA HB) as FB.
  pose proof (family_from_ctx _ _ _ _ _ _ _ _ _ _ E G G TB HC) as FC.
  exists (d_pi a ρ B), (d_pi b ρ B'); repeat split; eauto with mctt.
  exists (pi_rel R (fib ρ ρ B B)), (pi_rel R (fib ρ ρ B' B')); repeat split.
  - exists i; eapply at_pi; eassumption.
  - exists i; eapply at_pi; eassumption.
  - intros f g H x y K.
    destruct (H _ _ K) as (u & v & Fu & Fv & L).
    exists u, v; repeat split; auto.
    exact (family_sub _ _ _ _ _ _ _ _ E G TB FC HS _ _ K _ _ L).
Qed.

Local Lemma subtyp_sigma Γ A A' B B' i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A') ->
  (forall ρ ξ, env_rel (A :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B B) ->
  (forall ρ ξ, env_rel (A' :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B' B') ->
  sem_subtyp (A' :: Γ) B B' -> sem_subtyp Γ (a_sigma A B) (a_sigma A' B').
Proof.
  intros HA HB HC HS ρ E.
  destruct (HA _ _ E) as (a & b & F & G & R & T).
  pose proof (same_at _ _ _ _ T) as TA.
  pose proof (same_at _ _ _ _ (at_sym _ _ _ _ T)) as TB.
  pose proof (family_from_ctx _ _ _ _ _ _ _ _ _ _ E F F TA HB) as FB.
  pose proof (family_from_ctx _ _ _ _ _ _ _ _ _ _ E G G TB HC) as FC.
  exists (d_sigma a ρ B), (d_sigma b ρ B'); repeat split; eauto with mctt.
  exists (sigma_rel R (fib ρ ρ B B)), (sigma_rel R (fib ρ ρ B' B')); repeat split.
  - exists i; eapply at_sigma; eassumption.
  - exists i; eapply at_sigma; eassumption.
  - intros f g (x & y & u & v & Fx & Fy & K & Fu & Fv & L).
    exists x, y, u, v; repeat split; auto.
    exact (family_sub _ _ _ _ _ _ _ _ E G TB FC HS _ _ K _ _ L).
Qed.

Local Lemma form_pi_sub Γ Δ A B σ i :
  sem_sub Γ Δ σ σ ->
  (forall ρ ξ, env_rel Δ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (A :: Δ) ρ ξ -> eval_rel (universe i) ρ ξ B B) ->
  forall ρ ξ, env_rel Γ ρ ξ ->
    eval_rel (universe i) ρ ξ (a_sub (a_pi A B) σ) (a_pi (a_sub A σ) (a_sub B (Syntax.q σ))).
Proof.
  intros HS HA HB ρ ξ E.
  destruct (HS _ _ E) as (η & θ & F & G & K).
  destruct (HA _ _ K) as (a & b & Fa & Fb & R & T).
  exists (d_pi a η B), (d_pi b ξ (a_sub B (Syntax.q σ))); repeat split; eauto with mctt.
  eexists; apply at_pi with (R := R); [exact T |].
  intros x y L.
  assert (K' : env_rel (A :: Δ) (η ▻ x) (θ ▻ y)) by (eapply env_cons_at; eassumption).
  destruct (HB _ _ K') as (u & v & Fu & Fv & R' & U).
  exists u, v; repeat split; eauto with mctt. now exists R'.
Qed.

Local Lemma form_sigma_sub Γ Δ A B σ i :
  sem_sub Γ Δ σ σ ->
  (forall ρ ξ, env_rel Δ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (A :: Δ) ρ ξ -> eval_rel (universe i) ρ ξ B B) ->
  forall ρ ξ, env_rel Γ ρ ξ ->
    eval_rel (universe i) ρ ξ (a_sub (a_sigma A B) σ) (a_sigma (a_sub A σ) (a_sub B (Syntax.q σ))).
Proof.
  intros HS HA HB ρ ξ E.
  destruct (HS _ _ E) as (η & θ & F & G & K).
  destruct (HA _ _ K) as (a & b & Fa & Fb & R & T).
  exists (d_sigma a η B), (d_sigma b ξ (a_sub B (Syntax.q σ))); repeat split; eauto with mctt.
  eexists; apply at_sigma with (R := R); [exact T |].
  intros x y L.
  assert (K' : env_rel (A :: Δ) (η ▻ x) (θ ▻ y)) by (eapply env_cons_at; eassumption).
  destruct (HB _ _ K') as (u & v & Fu & Fv & R' & U).
  exists u, v; repeat split; eauto with mctt. now exists R'.
Qed.

Local Lemma fn_sub Γ Δ A B M σ i :
  sem_sub Γ Δ σ σ ->
  (forall ρ ξ, env_rel Δ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  sem_exp (A :: Δ) B M M ->
  sem_exp Γ (a_sub (a_pi A B) σ) (a_sub (a_fn A M) σ)
    (a_fn (a_sub A σ) (a_sub M (Syntax.q σ))).
Proof.
  intros HS HA [j HM]; exists (Nat.max i j); intros ρ ξ E.
  destruct (HS _ _ E) as (η & θ & F & G & K).
  destruct (HA _ _ K) as (a & b & Fa & Fb & R & T).
  assert (HB : family_at (Nat.max i j) R η θ B B).
  { intros x y L.
    assert (K' : env_rel (A :: Δ) (η ▻ x) (θ ▻ y)) by (eapply env_cons_at; eassumption).
    destruct (HM _ _ K') as (u & v & S & Fu & Fv & U & _).
    exists u, v; repeat split; auto.
    exists S; eapply sem_lift; [apply Nat.le_max_r | exact U]. }
  exists (d_pi a η B), (d_pi b θ B), (pi_rel R (fib η θ B B)); repeat split; eauto with mctt.
  - apply at_pi; [eapply sem_lift; [apply Nat.le_max_l | exact T] | exact HB].
  - exists (d_fn η M), (d_fn ξ (a_sub M (Syntax.q σ))); repeat split; eauto with mctt.
    intros x y L.
    assert (K' : env_rel (A :: Δ) (η ▻ x) (θ ▻ y)) by (eapply env_cons_at; eassumption).
    destruct (HM _ _ K') as (u & v & S & Fu & Fv & U & m & n & Fm & Fn & Hmn).
    exists m, n; repeat split; eauto 7 with mctt.
    exists u, v, S; repeat split; auto. now exists j.
Qed.

Local Ltac invert_evaluation :=
  repeat match goal with
  | H : eval_exp (a_sub _ _) _ _ |- _ => inversion H; clear H; subst
  | H : eval_sub a_id _ _ |- _ => inversion H; clear H; subst
  | H : eval_sub (a_extend _ _) _ _ |- _ => inversion H; clear H; subst
  | H : eval_exp (a_succ _) _ _ |- _ => inversion H; clear H; subst
  | H : eval_exp (a_app _ _) _ _ |- _ => inversion H; clear H; subst
  | H : eval_exp (a_pair _ _ _ _) _ _ |- _ => inversion H; clear H; subst
  | H : eval_exp (a_fst _) _ _ |- _ => inversion H; clear H; subst
  | H : eval_exp (a_snd _) _ _ |- _ => inversion H; clear H; subst
  | H : eval_exp (a_eq _ _ _) _ _ |- _ => inversion H; clear H; subst
  | H : eval_exp (a_refl _ _) _ _ |- _ => inversion H; clear H; subst
  | H : eval_fst (d_pair _ _) _ |- _ => inversion H; clear H; subst
  | H : eval_snd (d_pair _ _) _ |- _ => inversion H; clear H; subst
  end.

Local Ltac just_evaluation :=
  intros ? ? ?; invert_evaluation; solve [eauto 8 with mctt].

Local Lemma sem_id Γ : sem_sub Γ Γ a_id a_id.
Proof. intros ρ ξ K; exists ρ, ξ; auto with mctt. Qed.

Local Lemma sem_weaken Γ A : sem_sub (A :: Γ) Γ a_weaken a_weaken.
Proof.
  intros ρ ξ [K _]; exists (drop_env ρ), (drop_env ξ); auto with mctt.
Qed.

Local Lemma pi_beta Γ A B M N i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  sem_exp (A :: Γ) B M M -> sem_exp Γ A N N ->
  sem_exp Γ (a_sub B (a_extend a_id N)) (a_app (a_fn A M) N) (a_sub M (a_extend a_id N)).
Proof.
  intros HA HM HN.
  assert (HS : sem_sub Γ (A :: Γ) (a_extend a_id N) (a_extend a_id N)).
  { eapply sub_extend; [apply sem_id | exact HA |].
    eapply exp_transport; [exact HN | | |]; eauto with mctt. }
  eapply exp_transport; [exact (sem_exp_substitute _ _ _ _ _ _ _ HM HS) | | |];
    try solve [eauto with mctt].
  just_evaluation.
Qed.

(* The natural number recursor preserves the relation on its motive,
   including when evaluation constructs a neutral recursor. *)
Local Definition nat_data i ρ ξ A C Z Z' M M' :=
  family_at i nat_rel ρ ξ A C /\
  eval_rel (fib ρ ξ A C d_zero d_zero) ρ ξ Z Z' /\
  (forall x y, nat_rel x y -> forall u v, fib ρ ξ A C x y u v ->
      eval_rel (fib ρ ξ A C (d_succ x) (d_succ y)) (ρ ▻ x ▻ u) (ξ ▻ y ▻ v) M M').

Local Lemma natrec_neutral i ρ ξ A C Z Z' M M' z z' n n' :
  nat_data i ρ ξ A C Z Z' M M' ->
  fib ρ ξ A C d_zero d_zero z z' -> neutral n n' ->
  neutral (d_natrec ρ A z M n) (d_natrec ξ C z' M' n').
Proof.
  intros [Fam [_ Step]] HZ HN s.
  set (x := d_neut d_nat (d_var s)).
  assert (K : nat_rel x x) by (constructor; apply neutral_var).
  destruct (Fam _ _ K) as (b & b' & Fb & Fb' & R & T).
  pose proof (sem_quote _ _ _ (ex_intro _ i T)) as [QB [QN Qr]].
  destruct (QB (S s)) as (B & LB & RB).
  destruct HZ as (c & c' & U & Fc & Fc' & V & Lz).
  destruct (proj1 (proj2 (sem_quote _ _ _ V)) _ _ Lz s) as (BZ & LZ & RZ).
  assert (Kw : fib ρ ξ A C x x (d_neut b (d_var (S s))) (d_neut b' (d_var (S s)))).
  { exists b, b', R; repeat split; auto.
    - now exists i.
    - apply Qr, neutral_var. }
  destruct (Step _ _ K _ _ Kw)
    as (u & v & Fu & Fv & d & d' & S' & Fd & Fd' & W & L).
  destruct (proj1 (proj2 (sem_quote _ _ _ W)) _ _ L (S (S s))) as (BS & LS & RS).
  destruct (HN s) as (N & LN & RN).
  unfold x in *; quote_exists.
Qed.

Local Lemma natrec_values i ρ ξ A C Z Z' M M' :
  nat_data i ρ ξ A C Z Z' M M' ->
  forall x y, nat_rel x y ->
  exists u v, eval_natrec A Z M x ρ u /\ eval_natrec C Z' M' y ξ v /\
    fib ρ ξ A C x y u v.
Proof.
  intros D x y K; induction K as [| x y K IH | a b n n' N];
    destruct D as [Fam [Base Step]].
  - destruct Base as (u & v & ? & ? & L).
    exists u, v; repeat split; eauto with mctt.
  - destruct IH as (u & v & Fu & Fv & L).
    destruct (Step _ _ K _ _ L) as (w & w' & Fw & Fw' & L').
    exists w, w'; repeat split; eauto with mctt.
  - destruct Base as (z & z' & Fz & Fz' & Lz).
    assert (K : nat_rel (d_neut a n) (d_neut b n')) by (constructor; assumption).
    destruct (Fam _ _ K) as (c & c' & Fc & Fc' & R & T).
    do 2 eexists; repeat split; [eapply eval_natrec_neut; eassumption |
      eapply eval_natrec_neut; eassumption |].
    exists c, c', R; repeat split; auto.
    + now exists i.
    + apply (proj2 (proj2 (sem_quote _ _ _ (ex_intro _ i T)))).
      apply (natrec_neutral i ρ ξ A C Z Z' M M' z z' n n'); [refine (conj Fam (conj _ Step)) | exact Lz | exact N].
      exists z, z'; auto.
Qed.

Local Definition nat_step_sub :=
  a_extend (a_compose a_weaken a_weaken) (a_succ (a_var 1)).

Local Lemma nat_case_data Γ A C Z Z' M M' i :
  (forall ρ ξ, env_rel (a_nat :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (a_nat :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ A C) ->
  sem_exp Γ (a_sub A (a_extend a_id a_zero)) Z Z' ->
  sem_exp (A :: a_nat :: Γ) (a_sub A nat_step_sub) M M' ->
  forall ρ ξ, env_rel Γ ρ ξ -> nat_data i ρ ξ A C Z Z' M M'.
Proof.
  intros HA HC HZ HM ρ ξ E.
  assert (Fam : family_at i nat_rel ρ ξ A C) by (intros x y H; apply HC, env_nat; assumption).
  split; [exact Fam | split].
  - pose proof nat_rel_zero as K.
    destruct (Fam _ _ K) as (b & c & Fb & Fc & R & T).
    assert (F : eval_exp (a_sub A (a_extend a_id a_zero)) ρ b) by (eauto with mctt).
    destruct (terms_with _ _ _ _ _ _ _ _ _ _ HZ E F T) as (u & v & Fu & Fv & L).
    exists u, v; repeat split; auto.
    exists b, c, R; repeat split; auto. now exists i.
  - intros x y K u v L.
    destruct L as (b & c & R & Fb & Fc & T & L).
    pose proof (env_nat _ _ _ _ _ E K) as Ex.
    destruct (HA _ _ Ex) as (b0 & b' & Fb0 & Fb' & S' & U); same_eval.
    assert (EE : R ≃ S') by (eapply sem_coh; [exact T | exact (ex_intro _ i U) | auto]).
    assert (Ek : env_rel (A :: a_nat :: Γ) (ρ ▻ x ▻ u) (ξ ▻ y ▻ v)).
    { eapply env_cons_at; try eassumption. apply EE, L. }
    destruct (Fam _ _ (nat_rel_succ _ _ K)) as (cs & ds & Fcs & Fds & S & V).
    assert (FS : eval_sub nat_step_sub (ρ ▻ x ▻ u) (ρ ▻ d_succ x)).
    { unfold nat_step_sub. constructor; eauto 7 with mctt. }
    assert (F : eval_exp (a_sub A nat_step_sub) (ρ ▻ x ▻ u) cs)
      by (eapply eval_exp_sub; eassumption).
    destruct (terms_with _ _ _ _ _ _ _ _ _ _ HM Ek F V) as (r & r' & Fr & Fr' & H).
    exists r, r'; repeat split; auto.
    exists cs, ds, S; repeat split; auto. now exists i.
Qed.

Local Lemma term_natrec Γ A C Z Z' M M' N N' i :
  (forall ρ ξ, env_rel (a_nat :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (a_nat :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ A C) ->
  sem_exp Γ (a_sub A (a_extend a_id a_zero)) Z Z' ->
  sem_exp (A :: a_nat :: Γ) (a_sub A nat_step_sub) M M' ->
  sem_exp Γ a_nat N N' ->
  sem_exp Γ (a_sub A (a_extend a_id N)) (a_natrec A Z M N) (a_natrec C Z' M' N').
Proof.
  intros HA HC HZ HM HN; exists i; intros ρ ξ E.
  destruct (proj1 (sem_exp_nat _ _ _) HN _ _ E) as (x & y & Fx & Fy & K).
  destruct (proj1 (sem_exp_nat _ _ _) (sem_exp_left _ _ _ _ HN) _ _ E)
    as (x0 & y0 & Fx0 & Fy0 & K0); same_eval.
  pose proof (nat_case_data _ _ _ _ _ _ _ _ HA HC HZ HM _ _ E) as D.
  destruct (natrec_values _ _ _ _ _ _ _ _ _ D _ _ K)
    as (u & v & Fu & Fv & b & c & R & Fb & Fc & T & L).
  destruct (HA _ _ (env_nat _ _ _ _ _ E K0)) as (b0 & c0 & Fb0 & Fc0 & S' & U); same_eval.
  assert (Coh : R ≃ S') by (eapply sem_coh; [exact T | exact (ex_intro _ i U) | auto]).
  exists b, c0, S'; repeat split; eauto 7 with mctt.
  exists u, v; repeat split; eauto with mctt. apply Coh, L.
Qed.

Local Lemma nat_beta_succ Γ A Z M N i :
  (forall ρ ξ, env_rel (a_nat :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  sem_exp Γ (a_sub A (a_extend a_id a_zero)) Z Z ->
  sem_exp (A :: a_nat :: Γ) (a_sub A nat_step_sub) M M ->
  sem_exp Γ a_nat N N ->
  sem_exp Γ (a_sub A (a_extend a_id (a_succ N))) (a_natrec A Z M (a_succ N))
    (a_sub M (a_extend (a_extend a_id N) (a_natrec A Z M N))).
Proof.
  intros HA HZ HM HN; exists i; intros ρ ξ E.
  destruct (proj1 (sem_exp_nat _ _ _) HN _ _ E) as (x & y & Fx & Fy & K).
  pose proof (nat_case_data _ _ _ _ _ _ _ _ HA HA HZ HM _ _ E) as D.
  destruct (natrec_values _ _ _ _ _ _ _ _ _ D _ _ K) as (u & v & Fu & Fv & L).
  destruct D as [Fam [_ Step]].
  destruct (Step _ _ K _ _ L) as (r & r' & Fr & Fr' & b & c & R & Fb & Fc & T & L').
  destruct T as [j T].
  destruct (Fam _ _ (nat_rel_succ _ _ K)) as (b0 & c0 & Fb0 & Fc0 & R' & U); same_eval.
  assert (Coh : R ≃ R') by (eapply at_coh; [exact T | exact U | auto]).
  exists b, c, R'; repeat split; eauto 8 with mctt.
  exists r, r'; repeat split; eauto 9 with mctt. apply Coh, L'.
Qed.

Local Lemma nat_beta_zero Γ A Z M :
  sem_exp Γ (a_sub A (a_extend a_id a_zero)) Z Z ->
  sem_exp Γ (a_sub A (a_extend a_id a_zero)) (a_natrec A Z M a_zero) Z.
Proof.
  intro H; eapply exp_transport; [exact H | | |]; eauto 5 with mctt.
  intros ρ r F; eauto with mctt.
Qed.

Local Lemma eval_unsub M σ ρ ξ x :
  eval_sub σ ρ ξ -> eval_exp (a_sub M σ) ρ x -> eval_exp M ξ x.
Proof.
  intros F H. destruct (eval_sub_exp_inv _ _ _ _ H) as (ξ' & G & K).
  now rewrite (sub_unique _ _ _ _ F G).
Qed.

Local Lemma fib_push ρ ξ θ A C σ x y :
  eval_sub σ ξ θ ->
  fib ρ θ A C x y ≃ fib ρ ξ A (a_sub C (Syntax.q σ)) x y.
Proof.
  intros F u v; split; intros (b & c & R & Fb & Fc & T & L);
    exists b, c, R; repeat split; auto with mctt.
  - eapply eval_exp_sub; [exact (eval_q _ _ _ _ F) | exact Fc].
  - eapply eval_unsub; [exact (eval_q _ _ _ _ F) | exact Fc].
Qed.

Local Lemma nat_push i ρ ξ θ A C Z Z' M M' σ :
  eval_sub σ ξ θ -> nat_data i ρ θ A C Z Z' M M' ->
  nat_data i ρ ξ A (a_sub C (Syntax.q σ)) Z (a_sub Z' σ) M
    (a_sub M' (Syntax.q (Syntax.q σ))).
Proof.
  intros F [Fam [Base Step]]; split; [| split].
  - intros x y K. destruct (Fam _ _ K) as (b & c & Fb & Fc & R & T).
    exists b, c; repeat split; eauto with mctt. now exists R.
  - destruct Base as (u & v & Fz & Fz' & L).
    exists u, v; repeat split; eauto with mctt. apply (fib_push _ _ _ _ _ _ _ _ F), L.
  - intros x y K u v L.
    apply (fib_push _ _ _ _ _ _ _ _ F) in L.
    destruct (Step _ _ K _ _ L) as (b & c & Fb & Fc & W).
    exists b, c; repeat split; eauto 6 with mctt.
    apply (fib_push _ _ _ _ _ _ _ _ F), W.
Qed.

Local Lemma natrec_sub Γ Δ A Z M N σ i :
  sem_sub Γ Δ σ σ ->
  (forall ρ ξ, env_rel (a_nat :: Δ) ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  sem_exp Δ (a_sub A (a_extend a_id a_zero)) Z Z ->
  sem_exp (A :: a_nat :: Δ) (a_sub A nat_step_sub) M M ->
  sem_exp Δ a_nat N N ->
  sem_exp Γ (a_sub A (a_extend σ (a_sub N σ))) (a_sub (a_natrec A Z M N) σ)
     (a_natrec (a_sub A (Syntax.q σ)) (a_sub Z σ) (a_sub M (Syntax.q (Syntax.q σ))) (a_sub N σ)).
Proof.
  intros HS HA HZ HM HN; exists i; intros ρ ξ E.
  destruct (HS _ _ E) as (η & θ & F & G & E').
  destruct (proj1 (sem_exp_nat _ _ _) HN _ _ E') as (x & y & Fx & Fy & K).
  pose proof (nat_case_data _ _ _ _ _ _ _ _ HA HA HZ HM _ _ E') as D.
  pose proof (nat_push _ _ _ _ _ _ _ _ _ _ _ G D) as D'.
  destruct (natrec_values _ _ _ _ _ _ _ _ _ D' _ _ K) as (u & v & Fu & Fv & L).
  apply (fib_push _ _ _ _ _ _ _ _ G) in L.
  destruct L as (b & c & R & Fb & Fc & T & L).
  destruct (HA _ _ (env_nat _ _ _ _ _ E' K)) as (b0 & c0 & Fb0 & Fc0 & S' & U); same_eval.
  assert (Coh : R ≃ S') by (eapply sem_coh; [exact T | exact (ex_intro _ i U) | auto]).
  exists b, c, S'; repeat split; eauto 8 with mctt.
  exists u, v; repeat split; eauto 9 with mctt. apply Coh, L.
Qed.

Local Notation "'Ev3' B ρ x y n b" :=
  (eval_exp B (ρ ▻ x ▻ y ▻ n) b)
  (at level 10, B at level 0, ρ at level 0, x at level 0, y at level 0,
   n at level 0, b at level 0).

(* An equality recursor uses the motive at both endpoints and the proof.
   For reflexivity, the PER connects those endpoints to the branch input. *)
Local Definition eq_fib ρ ξ B C x x' y y' n n' : drel := fun u v =>
  exists b c R, Ev3 B ρ x y n b /\ Ev3 C ξ x' y' n' c /\ any_ty b c R /\ R u v.

Local Definition eq_motive j ρ ξ R B C :=
  forall x x' (L : R x x') y y' (K : R y y') n n',
    eq_rel R x y n n' ->
    eval_rel (universe j) (ρ ▻ x ▻ y ▻ n) (ξ ▻ x' ▻ y' ▻ n') B C.

Local Definition eq_branch ρ ξ R B C M M' :=
  forall x y, R x y ->
  eval_rel (eq_fib ρ ξ B C x y x y (d_refl x) (d_refl y)) (ρ ▻ x) (ξ ▻ y) M M'.

Local Lemma eqrec_neutral i j ρ ξ a b R B C M M' x x' y y' n n' :
  sem_ty i a b R -> eq_motive j ρ ξ R B C -> eq_branch ρ ξ R B C M M' ->
  R x x' -> R y y' -> neutral n n' ->
  neutral (d_eqrec ρ a B M x y n) (d_eqrec ξ b C M' x' y' n').
Proof.
  intros T Mot Branch Hx Hy Hn s.
  pose proof (sem_quote _ _ _ (ex_intro _ i T)) as [QT [QN QR]].
  destruct (QT s) as (A & ? & ?), (QN _ _ Hx s) as (X & ? & ?),
    (QN _ _ Hy s) as (Y & ? & ?), (Hn s) as (N & ? & ?).
  set (u := d_neut a (d_var s)). set (u' := d_neut b (d_var s)).
  set (v := d_neut a (d_var (S s))). set (v' := d_neut b (d_var (S s))).
  assert (U : R u u') by (apply QR, neutral_var).
  assert (V : R v v') by (apply QR, neutral_var).
  set (p := d_neut (d_eq a u v) (d_var (S (S s)))).
  set (p' := d_neut (d_eq b u' v') (d_var (S (S s)))).
  assert (P : eq_rel R u v p p') by (constructor; apply neutral_var).
  destruct (Mot _ _ U _ _ V _ _ P) as (c & c' & Fc & Fc' & R' & TC).
  destruct (proj1 (sem_quote _ _ _ (ex_intro _ j TC)) (S (S (S s)))) as (W & ? & ?).
  destruct (Branch _ _ U) as (e & e' & Fe & Fe' & d & d' & S' & Fd & Fd' & TD & L).
  destruct (proj1 (proj2 (sem_quote _ _ _ TD)) _ _ L (S s)) as (V' & ? & ?).
  unfold p, p', u, u', v, v' in *; quote_exists.
Qed.

Local Lemma eqrec_values i j ρ ξ a b R B C M M' :
  sem_ty i a b R -> eq_motive j ρ ξ R B C -> eq_branch ρ ξ R B C M M' ->
  forall x x', R x x' -> forall y y', R y y' -> forall n n', eq_rel R x y n n' ->
  exists u v, eval_eqrec a B M x y n ρ u /\ eval_eqrec b C M' x' y' n' ξ v /\
    eq_fib ρ ξ B C x x' y y' n n' u v.
Proof.
  intros T Mot Branch x x' Hx y y' Hy n n' Hn.
  destruct (Mot _ _ Hx _ _ Hy _ _ Hn) as (c & c' & Fc & Fc' & R' & TC).
  destruct Hn as [p p' L Lx Ly | c0 c0' m m' N].
  - destruct (at_per _ _ _ _ T) as [Sym Tr].
    assert (Kx : R x p') by (eapply Tr; [apply Sym, Lx | exact L]).
    assert (Ky : R y p') by (eapply Tr; [apply Sym, Ly | exact L]).
    assert (K : eq_rel R x y (d_refl p) (d_refl p')) by (constructor; assumption).
    destruct (Mot _ _ Kx _ _ Ky _ _ K) as (d & d' & Fd & Fd' & S' & TD).
    destruct (Branch _ _ L) as (u & v & Fu & Fv & e & e' & U & Fe & Fe' & TE & Huv).
    same_eval.
    assert (C1 : U ≃ S') by (eapply sem_coh; [exact TE | exact (ex_intro _ j TD) | auto]).
    assert (C2 : S' ≃ R') by (eapply at_coh; [exact TD | exact TC | auto]).
    exists u, v; repeat split; eauto with mctt.
    exists c, c', R'; repeat split; auto.
    + now exists j.
    + apply C2, C1, Huv.
  - do 2 eexists; repeat split; [eapply eval_eqrec_neut; eassumption |
      eapply eval_eqrec_neut; eassumption |].
    exists c, c', R'; repeat split; auto.
    + now exists j.
    + apply (proj2 (proj2 (sem_quote _ _ _ (ex_intro _ j TC)))).
      eapply eqrec_neutral; eassumption.
Qed.

Local Definition eq_ctx Γ A :=
  a_eq (a_sub A (a_compose a_weaken a_weaken)) (a_var 1) (a_var 0)
    :: a_sub A a_weaken :: A :: Γ.
Local Definition eq_branch_sub A :=
  a_extend (a_extend a_id (a_var 0)) (a_refl (a_sub A a_weaken) (a_var 0)).
Local Definition eq_arg_sub σ X Y N := a_extend (a_extend (a_extend σ X) Y) N.

Local Lemma eq_wk ρ A x a :
  eval_exp A ρ a -> eval_exp (a_sub A a_weaken) (ρ ▻ x) a.
Proof. eauto with mctt. Qed.
Local Hint Resolve eq_wk : mctt.

Local Lemma eq_wk2 ρ A x y a :
  eval_exp A ρ a -> eval_exp (a_sub A (a_compose a_weaken a_weaken)) (ρ ▻ x ▻ y) a.
Proof. eauto 7 with mctt. Qed.
Local Hint Resolve eq_wk2 : mctt.

Local Lemma env_eq_args Γ A i ρ ξ a b R :
  env_rel Γ ρ ξ -> eval_exp A ρ a -> eval_exp A ξ b -> sem_ty i a b R ->
  forall x x', R x x' -> forall y y', R y y' -> forall n n', eq_rel R x y n n' ->
  env_rel (eq_ctx Γ A) (ρ ▻ x ▻ y ▻ n) (ξ ▻ x' ▻ y' ▻ n').
Proof.
  intros E F G T x x' X y y' Y n n' N.
  unfold eq_ctx.
  eapply env_cons_at with (R := eq_rel R x y); [| eauto 7 with mctt | eauto 7 with mctt |
    exact (at_eq _ _ _ _ _ _ _ _ T X Y) | exact N].
  eapply env_cons_at; [| eauto with mctt | eauto with mctt | exact T | exact Y].
  eapply env_cons_at; eassumption.
Qed.

Local Lemma eq_motive_ctx Γ A B C i j ρ ξ a b R :
  env_rel Γ ρ ξ -> eval_exp A ρ a -> sem_ty i a b R ->
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (eq_ctx Γ A) ρ ξ -> eval_rel (universe j) ρ ξ B C) ->
  eq_motive j ρ ξ R B C.
Proof.
  intros E F T HA HB x x' X y y' Y n n' N.
  destruct (HA _ _ E) as (a0 & b0 & F0 & G0 & S' & U); same_eval.
  assert (Coh : R ≃ S') by (eapply at_coh; [exact T | exact U | auto]).
  assert (Eeq : eq_rel R x y ≃ eq_rel S' x y) by (apply eq_equiv; [exact Coh | intro; apply Coh | intro; apply Coh]).
  apply HB; eapply env_eq_args; [exact E | exact F | exact G0 | exact U | | |];
    [apply Coh, X | apply Coh, Y | apply Eeq, N].
Qed.

Local Lemma eq_branch_ctx Γ A B C M M' i j ρ ξ a b R :
  env_rel Γ ρ ξ -> eval_exp A ρ a -> sem_ty i a b R ->
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  eq_motive j ρ ξ R B C ->
  sem_exp (A :: Γ) (a_sub B (eq_branch_sub A)) M M' ->
  eq_branch ρ ξ R B C M M'.
Proof.
  intros E F T HA Mot HM x y X.
  destruct (HA _ _ E) as (a0 & b0 & F0 & G0 & S' & U); same_eval.
  assert (Coh : R ≃ S') by (eapply at_coh; [exact T | exact U | auto]).
  assert (Ex : env_rel (A :: Γ) (ρ ▻ x) (ξ ▻ y))
    by (eapply env_cons_at; try eassumption; apply Coh, X).
  assert (Re : eq_rel R x x (d_refl x) (d_refl y)).
  { assert (X0 : R x x) by exact (per_left _ (at_per _ _ _ _ T) _ _ X).
    constructor; assumption. }
  destruct (Mot _ _ X _ _ X _ _ Re) as (c & c' & Fc & Fc' & S & V).
  assert (Fsub : eval_sub (eq_branch_sub A) (ρ ▻ x) (ρ ▻ x ▻ x ▻ d_refl x)).
  { unfold eq_branch_sub; eauto 7 with mctt. }
  assert (Fty : eval_exp (a_sub B (eq_branch_sub A)) (ρ ▻ x) c)
    by (eapply eval_exp_sub; eassumption).
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HM Ex Fty V) as (r & r' & Fr & Fr' & L).
  exists r, r'; repeat split; auto.
  exists c, c', S; repeat split; auto. now exists j.
Qed.

Local Lemma eq_args Γ A X X' Y Y' N N' i ρ ξ a b R :
  env_rel Γ ρ ξ -> eval_exp A ρ a -> sem_ty i a b R ->
  sem_exp Γ A X X' -> sem_exp Γ A Y Y' -> sem_exp Γ (a_eq A X Y) N N' ->
  exists x x' y y' n n', eval_exp X ρ x /\ eval_exp X' ξ x' /\
    eval_exp Y ρ y /\ eval_exp Y' ξ y' /\ eval_exp N ρ n /\ eval_exp N' ξ n' /\
    R x x' /\ R y y' /\ eq_rel R x y n n'.
Proof.
  intros E F T HX HY HN.
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HX E F T) as (x & x' & Fx & Fx' & Kx).
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HY E F T) as (y & y' & Fy & Fy' & Ky).
  assert (F' : eval_exp (a_eq A X Y) ρ (d_eq a x y)) by (constructor; assumption).
  pose proof (at_eq _ _ _ _ _ _ _ _ T Kx Ky) as TE.
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HN E F' TE) as (n & n' & Fn & Fn' & K).
  exists x, x', y, y', n, n'; repeat split; assumption.
Qed.

Local Lemma term_eqrec Γ A A' B B' M M' X X' Y Y' N N' i j :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A') ->
  (forall ρ ξ, env_rel (eq_ctx Γ A) ρ ξ -> eval_rel (universe j) ρ ξ B B') ->
  sem_exp (A :: Γ) (a_sub B (eq_branch_sub A)) M M' ->
  sem_exp Γ A X X' -> sem_exp Γ A Y Y' -> sem_exp Γ (a_eq A X Y) N N' ->
  sem_exp Γ (a_sub B (eq_arg_sub a_id X Y N))
    (a_eqrec A B M X Y N) (a_eqrec A' B' M' X' Y' N').
Proof.
  intros HA HA' HB HM HX HY HN.
  assert (HB0 : forall ρ ξ, env_rel (eq_ctx Γ A) ρ ξ -> eval_rel (universe j) ρ ξ B B).
  { apply sem_exp_type, (sem_exp_left _ _ _ B'), sem_exp_type, HB. }
  exists j; intros ρ ξ E.
  destruct (HA' _ _ E) as (a & b & F & G & R & T).
  pose proof (eq_motive_ctx _ _ _ _ _ _ _ _ _ _ _ E F T HA HB) as Mot.
  pose proof (eq_motive_ctx _ _ _ _ _ _ _ _ _ _ _ E F T HA HB0) as Mot0.
  pose proof (eq_branch_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ E F T HA Mot HM) as Branch.
  destruct (eq_args _ _ _ _ _ _ _ _ _ _ _ _ _ _ E F T HX HY HN)
    as (x & x' & y & y' & n & n' & Fx & Fx' & Fy & Fy' & Fn & Fn' & Kx & Ky & Kn).
  destruct (eq_args _ _ _ _ _ _ _ _ _ _ _ _ _ _ E F T
    (sem_exp_left _ _ _ _ HX) (sem_exp_left _ _ _ _ HY) (sem_exp_left _ _ _ _ HN))
    as (x0 & x0' & y0 & y0' & n0 & n0' & Fx0 & Fx0' & Fy0 & Fy0' & Fn0 & Fn0' & Kx0 & Ky0 & Kn0).
  same_eval.
  destruct (eqrec_values _ _ _ _ _ _ _ _ _ _ _ T Mot Branch _ _ Kx _ _ Ky _ _ Kn)
    as (u & v & Fu & Fv & c & d & S & Fc & Fd & U & L).
  destruct (Mot0 _ _ Kx0 _ _ Ky0 _ _ Kn0) as (c0 & d0 & Fc0 & Fd0 & S' & V); same_eval.
  assert (Coh : S ≃ S') by (eapply sem_coh; [exact U | exact (ex_intro _ j V) | auto]).
  unfold eq_arg_sub.
  exists c, d0, S'; repeat split; eauto 8 with mctt.
  exists u, v; repeat split; eauto with mctt. apply Coh, L.
Qed.

Local Lemma eqrec_beta Γ A B M X i j :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (eq_ctx Γ A) ρ ξ -> eval_rel (universe j) ρ ξ B B) ->
  sem_exp (A :: Γ) (a_sub B (eq_branch_sub A)) M M ->
  sem_exp Γ A X X ->
  sem_exp Γ (a_sub B (eq_arg_sub a_id X X (a_refl A X)))
    (a_eqrec A B M X X (a_refl A X)) (a_sub M (a_extend a_id X)).
Proof.
  intros HA HB HM HX; exists j; intros ρ ξ E.
  destruct (HA _ _ E) as (a & b & F & G & R & T).
  pose proof (eq_motive_ctx _ _ _ _ _ _ _ _ _ _ _ E F T HA HB) as Mot.
  pose proof (eq_branch_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ E F T HA Mot HM) as Branch.
  destruct (terms_with _ _ _ _ _ _ _ _ _ _ HX E F T) as (x & y & Fx & Fy & K).
  assert (Re : eq_rel R x x (d_refl x) (d_refl y)).
  { assert (K0 : R x x) by exact (per_left _ (at_per _ _ _ _ T) _ _ K).
    constructor; assumption. }
  destruct (Branch _ _ K) as (u & v & Fu & Fv & c & c' & S & Fc & Fc' & U & L).
  destruct (Mot _ _ K _ _ K _ _ Re) as (c0 & c0' & Fc0 & Fc0' & S' & V); same_eval.
  assert (Coh : S ≃ S') by (eapply sem_coh; [exact U | exact (ex_intro _ j V) | auto]).
  unfold eq_arg_sub.
  exists c, c', S'; repeat split; eauto 9 with mctt.
  exists u, v; repeat split; eauto 6 with mctt. apply Coh, L.
Qed.

Local Definition lift3 σ := Syntax.q (Syntax.q (Syntax.q σ)).

Local Lemma eval_lift3 σ ξ θ x y z :
  eval_sub σ ξ θ ->
  eval_sub (lift3 σ) (ξ ▻ x ▻ y ▻ z) (θ ▻ x ▻ y ▻ z).
Proof. unfold lift3; auto 5 using eval_q. Qed.

Local Lemma eq_fib_push ρ ξ θ B C σ x x' y y' n n' :
  eval_sub σ ξ θ ->
  eq_fib ρ θ B C x x' y y' n n' ≃
  eq_fib ρ ξ B (a_sub C (lift3 σ)) x x' y y' n n'.
Proof.
  intros F u v; split; intros (b & c & R & Fb & Fc & T & L);
    exists b, c, R; repeat split; auto.
  - eapply eval_exp_sub; [exact (eval_lift3 _ _ _ _ _ _ F) | exact Fc].
  - eapply eval_unsub; [exact (eval_lift3 _ _ _ _ _ _ F) | exact Fc].
Qed.

Local Lemma eq_motive_push j ρ ξ θ R B C σ :
  eval_sub σ ξ θ -> eq_motive j ρ θ R B C ->
  eq_motive j ρ ξ R B (a_sub C (lift3 σ)).
Proof.
  intros F Mot x x' Kx y y' Ky n n' Kn.
  destruct (Mot _ _ Kx _ _ Ky _ _ Kn) as (b & c & Fb & Fc & R' & T).
  exists b, c; repeat split; auto.
  - eapply eval_exp_sub; [exact (eval_lift3 _ _ _ _ _ _ F) | exact Fc].
  - now exists R'.
Qed.

Local Lemma eq_branch_push ρ ξ θ R B C M M' σ :
  eval_sub σ ξ θ -> eq_branch ρ θ R B C M M' ->
  eq_branch ρ ξ R B (a_sub C (lift3 σ)) M (a_sub M' (Syntax.q σ)).
Proof.
  intros F Br x y L.
  destruct (Br _ _ L) as (u & v & Fu & Fv & K).
  exists u, v; repeat split; auto.
  - eapply eval_exp_sub; [exact (eval_q _ _ _ _ F) | exact Fv].
  - apply (eq_fib_push _ _ _ _ _ _ _ _ _ _ _ _ F), K.
Qed.

Local Lemma eqrec_sub Γ Δ A B M X Y N σ i j :
  sem_sub Γ Δ σ σ ->
  (forall ρ ξ, env_rel Δ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (eq_ctx Δ A) ρ ξ -> eval_rel (universe j) ρ ξ B B) ->
  sem_exp (A :: Δ) (a_sub B (eq_branch_sub A)) M M ->
  sem_exp Δ A X X -> sem_exp Δ A Y Y -> sem_exp Δ (a_eq A X Y) N N ->
  sem_exp Γ (a_sub B (eq_arg_sub σ (a_sub X σ) (a_sub Y σ) (a_sub N σ)))
    (a_sub (a_eqrec A B M X Y N) σ)
    (a_eqrec (a_sub A σ) (a_sub B (lift3 σ)) (a_sub M (Syntax.q σ))
      (a_sub X σ) (a_sub Y σ) (a_sub N σ)).
Proof.
  intros HS HA HB HM HX HY HN; exists j; intros ρ ξ E.
  destruct (HS _ _ E) as (η & θ & F & G & E').
  destruct (HA _ _ E') as (a & b & Fa & Fb & R & T).
  pose proof (eq_motive_ctx _ _ _ _ _ _ _ _ _ _ _ E' Fa T HA HB) as Mot.
  pose proof (eq_branch_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ E' Fa T HA Mot HM) as Br.
  pose proof (eq_motive_push _ _ _ _ _ _ _ _ G Mot) as Mot'.
  pose proof (eq_branch_push _ _ _ _ _ _ _ _ _ G Br) as Br'.
  destruct (eq_args _ _ _ _ _ _ _ _ _ _ _ _ _ _ E' Fa T HX HY HN)
    as (x & x' & y & y' & n & n' & Fx & Fx' & Fy & Fy' & Fn & Fn' & Kx & Ky & Kn).
  destruct (eqrec_values _ _ _ _ _ _ _ _ _ _ _ T Mot' Br' _ _ Kx _ _ Ky _ _ Kn)
    as (u & v & Fu & Fv & L).
  apply (eq_fib_push _ _ _ _ _ _ _ _ _ _ _ _ G) in L.
  destruct L as (c & d & S & Fc & Fd & U & L).
  destruct (Mot _ _ Kx _ _ Ky _ _ Kn) as (c0 & d0 & Fc0 & Fd0 & S' & V); same_eval.
  assert (Coh : S ≃ S') by (eapply sem_coh; [exact U | exact (ex_intro _ j V) | auto]).
  unfold eq_arg_sub.
  exists c, d, S'; repeat split; eauto 9 with mctt.
  exists u, v; repeat split; eauto 9 with mctt. apply Coh, L.
Qed.

Local Lemma sem_type Γ i : sem_exp Γ (a_typ (S i)) (a_typ i) (a_typ i).
Proof.
  apply sem_exp_type; intros ρ ξ E.
  exists (d_univ i), (d_univ i); repeat split; auto with mctt.
  exists (universe i); apply sem_univ; lia.
Qed.

Local Lemma sem_nat Γ : sem_exp Γ (a_typ 0) a_nat a_nat.
Proof.
  apply sem_exp_type; intros ρ ξ E.
  exists d_nat, d_nat; repeat split; auto with mctt.
  exists nat_rel; constructor; apply equiv_refl.
Qed.

Local Lemma sem_zero Γ : sem_exp Γ a_nat a_zero a_zero.
Proof.
  apply sem_exp_nat; intros ρ ξ E.
  exists d_zero, d_zero; repeat split; auto with mctt; constructor.
Qed.

Local Lemma sem_succ Γ M N :
  sem_exp Γ a_nat M N -> sem_exp Γ a_nat (a_succ M) (a_succ N).
Proof.
  intros H; apply sem_exp_nat; intros ρ ξ E.
  destruct (proj1 (sem_exp_nat _ _ _) H _ _ E) as (x & y & F & G & K).
  exists (d_succ x), (d_succ y); repeat split; auto with mctt; constructor; assumption.
Qed.

Local Ltac commute_evaluation :=
  intros ? ? ?;
  invert_evaluation;
  repeat match goal with
  | H : eval_exp (a_typ _) _ _ |- _ => inversion H; clear H; subst
  | H : eval_exp a_nat _ _ |- _ => inversion H; clear H; subst
  | H : eval_exp a_zero _ _ |- _ => inversion H; clear H; subst
  | H : eval_exp (a_var _) _ _ |- _ => inversion H; clear H; subst
  | H : eval_sub a_weaken _ _ |- _ => inversion H; clear H; subst
  end;
  solve [eauto 9 with mctt].

Local Ltac transport_from H :=
  eapply exp_transport; [exact H | | |];
  first [solve [auto with mctt] | commute_evaluation].

Local Lemma fst_beta Γ A B M N i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (A :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B B) ->
  sem_exp Γ A M M -> sem_exp Γ (a_sub B (a_extend a_id M)) N N ->
  sem_exp Γ A (a_fst (a_pair M A N B)) M.
Proof.
  intros HA HB HM HN.
  pose proof (term_pair _ _ A _ B _ _ _ _ _ HA HB HM HN) as P.
  pose proof (term_fst _ _ _ _ _ _ HA HB P) as E.
  transport_from E.
Qed.

Local Lemma snd_beta Γ A B M N i :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A) ->
  (forall ρ ξ, env_rel (A :: Γ) ρ ξ -> eval_rel (universe i) ρ ξ B B) ->
  sem_exp Γ A M M -> sem_exp Γ (a_sub B (a_extend a_id M)) N N ->
  sem_exp Γ (a_sub B (a_extend a_id M)) (a_snd (a_pair M A N B)) N.
Proof.
  intros HA HB HM HN.
  pose proof (term_pair _ _ A _ B _ _ _ _ _ HA HB HM HN) as P.
  pose proof (term_snd _ _ _ _ _ _ HA HB P) as E.
  transport_from E.
Qed.

Local Lemma var_zero_sub Γ A M σ :
  sem_exp Γ (a_sub A σ) M M ->
  sem_exp Γ (a_sub A σ) (a_sub (a_var 0) (a_extend σ M)) M.
Proof.
  intros [i H]; exists i; intros ρ ξ E.
  destruct (H _ _ E) as (a & b & R & F & G & T & x & y & Fx & Fy & K).
  destruct (eval_sub_exp_inv _ _ _ _ F) as (η & Fη & _).
  exists a, b, R; repeat split; auto.
  exists x, y; repeat split; eauto with mctt.
Qed.

Local Lemma var_succ_sub Γ Δ A B M σ x :
  sem_sub Γ Δ σ σ -> valid_ctx Δ -> ctx_lookup x B Δ ->
  sem_exp Γ (a_sub A σ) M M ->
  sem_exp Γ (a_sub B σ) (a_sub (a_var (S x)) (a_extend σ M)) (a_sub (a_var x) σ).
Proof.
  intros HS V H [i HM].
  destruct (sem_exp_substitute _ _ _ _ _ _ _ (lookup_sem _ _ _ H V) HS) as [j K].
  exists j; intros ρ ξ E.
  destruct (K _ _ E) as (a & b & R & F & G & T & u & v & Fu & Fv & L).
  destruct (HM _ _ E) as (_ & _ & _ & _ & _ & _ & m & _ & Fm & _ & _).
  destruct (eval_sub_exp_inv _ _ _ _ Fu) as (η & Fη & Fx).
  inversion Fx; subst.
  exists a, b, R; repeat split; auto.
  exists (η x), v; repeat split; eauto with mctt.
  eapply eval_exp_sub with (ρ' := η ▻ m); [apply eval_sub_extend; [exact Fη | exact Fm] |].
  change (eval_exp (a_var (S x)) (η ▻ m) ((η ▻ m) (S x))); constructor.
Qed.

Local Lemma var_wk Γ A B x :
  valid_ctx Γ -> ctx_lookup x A Γ ->
  sem_exp (B :: Γ) (a_sub A a_weaken) (a_sub (a_var x) a_weaken) (a_var (S x)).
Proof.
  intros V H.
  pose proof (sem_exp_substitute _ _ _ _ _ _ _ (lookup_sem _ _ _ H V) (sem_weaken Γ B)) as K.
  eapply exp_transport; [exact K | | |]; try solve [auto with mctt].
  intros ρ m Ev0. invert_evaluation.
  match goal with Hs : eval_sub a_weaken _ _, Hv : eval_exp (a_var _) _ _ |- _ =>
    inversion Hs; subst; inversion Hv; subst
  end.
  change (eval_exp (a_var (S x)) ρ (ρ (S x))); constructor.
Qed.

Local Lemma sub_transport Γ Δ σ τ υ ω :
  sem_sub Γ Δ σ τ ->
  (forall ρ η, eval_sub σ ρ η -> eval_sub υ ρ η) ->
  (forall ρ η, eval_sub τ ρ η -> eval_sub ω ρ η) ->
  sem_sub Γ Δ υ ω.
Proof.
  intros H F G ρ ξ K.
  destruct (H _ _ K) as (η & θ & Fη & Fθ & L).
  exists η, θ; auto.
Qed.

Local Ltac commute_substitution :=
  intros ? ? ?;
  repeat match goal with
  | H : eval_sub (a_compose _ _) _ _ |- _ => inversion H; clear H; subst
  | H : eval_sub (a_extend _ _) _ _ |- _ => inversion H; clear H; subst
  end;
  solve [eauto 8 with mctt].

Local Lemma sub_p_extend Γ Δ A M σ :
  sem_sub Γ Δ σ σ -> sem_exp Γ (a_sub A σ) M M ->
  sem_sub Γ Δ (a_compose a_weaken (a_extend σ M)) σ.
Proof.
  intros HS [i HM] ρ ξ E.
  destruct (HS _ _ E) as (η & θ & F & G & K).
  destruct (HM _ _ E) as (_ & _ & _ & _ & _ & _ & x & y & Fx & Fy & _).
  exists η, θ; repeat split; eauto 8 with mctt.
Qed.

Local Lemma sub_eta Γ Δ A σ :
  sem_sub Γ (A :: Δ) σ σ ->
  sem_sub Γ (A :: Δ) σ (a_extend (a_compose a_weaken σ) (a_sub (a_var 0) σ)).
Proof.
  intros HS ρ ξ E.
  destruct (HS _ _ E) as (η & θ & F & G & K).
  exists η, (drop_env θ ▻ θ 0); repeat split; eauto 8 with mctt.
  all: apply K.
Qed.

Local Lemma valid_tail Γ A : valid_ctx (A :: Γ) -> valid_ctx Γ.
Proof. inversion 1; assumption. Qed.

Local Ltac valid_context :=
  first [assumption | solve [eapply valid_extend; eassumption] |
    match goal with
    | H : valid_ctx (_ :: _) |- valid_ctx _ =>
      let K := fresh in pose proof (valid_tail _ _ H) as K; clear H; valid_context
    end | apply valid_empty].

Local Hint Resolve sem_type sem_nat sem_zero sem_succ sem_id sem_weaken
  lookup_sem valid_tail sem_exp_sym sem_exp_trans sem_sub_sym sem_sub_trans
  subtyp_trans subtyp_univ : semantic.

Local Hint Resolve sub_extend sub_compose ctx_sub_extend subtyp_exp subtyp_refl
  term_fn term_refl term_app term_pair term_fst term_snd pi_eta sigma_eta
  pi_beta fst_beta snd_beta fn_sub subtyp_pi subtyp_sigma
  term_natrec natrec_sub nat_beta_zero nat_beta_succ
  term_eqrec eqrec_sub eqrec_beta var_zero_sub var_succ_sub var_wk
  sub_p_extend sub_eta : semantic.

Local Hint Resolve form_pi form_sigma form_eq form_pi_sub form_sigma_sub : semantic.

Local Ltac substitute_then_transport H K :=
  let L := fresh in pose proof (sem_exp_substitute _ _ _ _ _ _ _ H K) as L;
  transport_from L.

Local Lemma type_left Γ i A B :
  (forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A B) ->
  forall ρ ξ, env_rel Γ ρ ξ -> eval_rel (universe i) ρ ξ A A.
Proof. intro H; apply sem_exp_type, (sem_exp_left _ _ _ B), sem_exp_type, H. Qed.

Local Lemma sub_context Γ Δ Δ' σ τ :
  sem_sub Γ Δ σ τ -> sem_ctx_sub Δ Δ' -> sem_sub Γ Δ' σ τ.
Proof.
  intros H K ρ ξ L. destruct (H _ _ L) as (η & θ & F & G & E).
  exists η, θ; auto.
Qed.

(* Substitution equality is interpreted in a valid target context. Its
   extension rule has no independent validity premise for that context. *)
Local Lemma fundamental :
  (forall Γ, wf_ctx Γ -> valid_ctx Γ) /\
  (forall Γ Δ, wf_ctx_sub Γ Δ -> valid_ctx Γ /\ sem_ctx_sub Γ Δ) /\
  (forall Γ A M, wf_exp Γ A M -> valid_ctx Γ /\ sem_exp Γ A M M) /\
  (forall Γ A M N, wf_exp_eq Γ A M N -> valid_ctx Γ /\ sem_exp Γ A M N) /\
  (forall Γ Δ σ, wf_sub Γ Δ σ -> valid_ctx Γ /\ valid_ctx Δ /\ sem_sub Γ Δ σ σ) /\
  (forall Γ Δ σ τ, wf_sub_eq Γ Δ σ τ -> valid_ctx Γ /\ (valid_ctx Δ -> sem_sub Γ Δ σ τ)) /\
  (forall Γ A B, wf_subtyp Γ A B -> valid_ctx Γ /\ sem_subtyp Γ A B).
Proof.
  apply syntactic_wf_mut_ind; intros;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat match goal with
    | H : sem_exp ?Γ (a_typ ?i) ?M ?N |- _ =>
        let K := fresh in
        pose proof (proj1 (sem_exp_type Γ i M N) H) as K; clear H; rename K into H
    end;
    repeat match goal with |- _ /\ _ => split end;
    try solve [valid_context];
    try match goal with |- valid_ctx _ -> _ => intros ? end;
    try solve [eauto 3 with semantic];
    try match goal with
    | |- sem_exp _ (a_typ _) _ _ => solve [apply sem_exp_type; eauto 3 with semantic]
    end.
  all: repeat match goal with
    | H : valid_ctx ?Δ -> sem_sub _ ?Δ _ _, V : valid_ctx ?Δ |- _ => specialize (H V)
    end.
  all: try solve [unfold sem_ctx_sub; auto].
  all: try solve [
    first [eapply sem_exp_substitute | eapply eqrec_sub | eapply term_eqrec | eapply eqrec_beta |
           eapply sub_compose | eapply sem_sub_trans];
    eassumption].
  - substitute_then_transport (sem_type Δ i) H1.
  - substitute_then_transport (sem_nat Δ) H1.
  - substitute_then_transport (sem_zero Δ) H1.
  - substitute_then_transport (sem_succ _ _ _ H1) H3.
  - substitute_then_transport (term_app _ _ _ _ _ _ _ _ H7 H6 H5 H4) H9.
  - eapply term_pair; [exact H8 | apply (type_left _ _ _ _ H6) | exact H5 | exact H4].
  - substitute_then_transport (term_pair _ _ A _ B _ _ _ _ _ H7 H6 H5 H4) H9.
  - substitute_then_transport (term_fst _ _ _ _ _ _ H5 H4 H3) H7.
  - substitute_then_transport (term_snd _ _ _ _ _ _ H5 H4 H3) H7.
  - assert (E : sem_exp Δ (a_typ i) (a_eq A M N) (a_eq A M N)).
    { apply sem_exp_type; exact (form_eq _ _ _ _ _ _ _ _ H5 H4 H3). }
    substitute_then_transport E H7.
  - substitute_then_transport (term_refl _ _ A _ _ _ H3 H2) H5.
  - eapply term_refl; [exact (type_left _ _ _ _ H2) | exact H1].
  - transport_from H0.
  - pose proof (sub_compose _ _ _ _ _ _ _ H6 H4) as HS.
    pose proof (sem_exp_substitute _ _ _ _ _ _ _ H2 HS) as HE.
    eapply exp_transport; [exact HE | | | intro; apply into_sub_compose]; auto with mctt.
  - eapply sub_context; eassumption.
  - eapply sub_transport; [exact H1 | |]; intros; eauto with mctt.
  - eapply sub_transport; [exact H1 | |]; intros; eauto with mctt.
  - pose proof (sub_compose _ _ _ _ _ _ _ H3 H5) as HS.
    pose proof (sub_compose _ _ _ _ _ _ _ HS H7) as HT.
    eapply sub_transport; [exact HT | commute_substitution | auto].
  - pose proof (sub_extend _ _ _ _ _ _ _ _ H8 H6 H5) as HS.
    pose proof (sub_compose _ _ _ _ _ _ _ H4 HS) as HT.
    eapply sub_transport; [exact HT | auto | commute_substitution].
  - eapply sub_context; eassumption.
Qed.

Theorem completeness : forall {Γ M M' A},
  {{ Γ ⊢ M ≈ M' : A }} ->
  exists W, nbe Γ M A W /\ nbe Γ M' A W.
Proof.
  intros Γ M M' A H.
  destruct (proj1 (proj2 (proj2 (proj2 fundamental))) _ _ _ _ H) as [V [i E]].
  destruct (valid_initial _ V) as (ρ & HI & HR).
  destruct (E _ _ HR) as (a & b & R & F & G & T & m & n & Fm & Fn & L).
  same_eval.
  destruct (proj1 (proj2 (sem_quote _ _ _ (ex_intro _ i T))) _ _ L (length Γ))
    as (W & Q & Q').
  exists W; split; eapply nbe_run; eassumption.
Qed.
