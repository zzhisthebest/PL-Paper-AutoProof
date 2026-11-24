From Stdlib Require Import List CRelationClasses.
Import ListNotations.

Set Implicit Arguments.

Notation "l · a" := (l ++ a :: nil) (at level 56, left associativity) : list_scope.
Infix "<=>" := iffT (at level 95, no associativity).

Fixpoint InT {A : Type} (a : A) (l : list A) : Type :=
  match l with
  | nil => False
  | b :: m => sum (b = a) (InT a m)
  end.

Definition Atom : Type := nat.

Inductive form := var (_ : Atom) | omega | inter (_ _ : form) | arrow (_ _ : form).

Notation Ω := omega.
Infix "∩" := inter (at level 35).
Infix "→" := arrow (right associativity, at level 39).

Reserved Notation "a ≤ b" (at level 70).

Inductive bcd_sub {lax : list (Atom -> form * form)} : crelation form :=
| bcd_identity a : a ≤ a
| bcd_trans a b c : a ≤ b -> b ≤ c -> a ≤ c
| bcd_omega_right a : a ≤ Ω
| bcd_inter_left1 a b : a ∩ b ≤ a
| bcd_inter_left2 a b : a ∩ b ≤ b
| bcd_inter_right a : a ≤ a ∩ a
| bcd_inter a b c d : a ≤ c -> b ≤ d -> a ∩ b ≤ c ∩ d
| bcd_arrow a b c d : c ≤ a -> b ≤ d -> a → b ≤ c → d
| bcd_arrow_inter a b c : (a → b) ∩ (a → c) ≤ a → b ∩ c
| bcd_arrow_omega : Ω ≤ Ω → Ω
| bcd_axiom ax x : InT ax lax -> fst (ax x) ≤ snd (ax x)
where "a ≤ b" := (bcd_sub a b).

Reserved Notation "a ❘ l ⊦ b" (at level 65, l at next level, b at next level).
Reserved Notation "a ❘ ⊦ b" (at level 65, b at next level).

Inductive sub : list form -> crelation form :=
| identity a : a ❘ ⊦ a
| omega_right a l : a ❘ l ⊦ Ω
| inter_left1 b a c l : a ❘ l ⊦ c -> a ∩ b ❘ l ⊦ c
| inter_left2 b a c l : a ❘ l ⊦ c -> b ∩ a ❘ l ⊦ c
| inter_right a b c l : c ❘ l ⊦ a -> c ❘ l ⊦ b -> c ❘ l ⊦ a ∩ b
| arrow_left a b c d l : c ❘ ⊦ a -> b ❘ l ⊦ d -> a → b ❘ c :: l ⊦ d
| arrow_right a b c l : c ❘ l · a ⊦ b -> c ❘ l ⊦ a → b
where "a ❘ l ⊦ b" := (sub l a b)
  and "a ❘ ⊦ b" := (sub nil a b).

Notation "a ⩽ b " := (@bcd_sub [] a b) (at level 70).

Lemma sub_replace_argument a a'
    (replace : forall b, a ❘ ⊦ b -> a' ❘ ⊦ b) :
  forall l s t, s ❘ l ⊦ t ->
    forall p q, l = p ++ a :: q -> s ❘ p ++ a' :: q ⊦ t.
Proof.
  intros l s t derivation.
  induction derivation; intros p q context_eq.
  - destruct p; discriminate.
  - apply omega_right.
  - apply inter_left1. now apply IHderivation.
  - apply inter_left2. now apply IHderivation.
  - apply inter_right; [now apply IHderivation1 | now apply IHderivation2].
  - destruct p as [|x p]; simpl in *; injection context_eq as head tail.
    + subst. apply arrow_left; [now apply replace | assumption].
    + subst. apply arrow_left; [assumption | now apply IHderivation2].
  - apply arrow_right.
    rewrite <- app_assoc. simpl.
    apply IHderivation. now rewrite context_eq, <- app_assoc.
Qed.

Definition sub_cut_at b :=
  forall a c l m, a ❘ l ⊦ b -> b ❘ m ⊦ c -> a ❘ l ++ m ⊦ c.

(* Move the cut past the last sequent rules until both act on the cut formula. *)
Lemma sub_cut_step b :
  (forall x y, b = x ∩ y -> (sub_cut_at x * sub_cut_at y)%type) ->
  (forall x y, b = x → y -> (sub_cut_at x * sub_cut_at y)%type) ->
  sub_cut_at b.
Proof.
  intros inter_cuts arrow_cuts a c l m left right.
  remember b as middle eqn:middle_eq in left.
  revert c m right.
  induction left as
    [s | s l | x s t l left IH | x s t l left IH |
     x y s l left_x IHx left_y IHy |
     x y s t l domain IHdomain codomain IHcodomain |
     x y s l left IH]; intros c m right; subst b.
  - exact right.
  - remember Ω as source eqn:source_eq in right.
    induction right; subst; try discriminate.
    + apply omega_right.
    + apply omega_right.
    + apply inter_right; auto.
    + apply arrow_right. rewrite <- app_assoc. auto.
  - apply inter_left1. now apply IH.
  - apply inter_left2. now apply IH.
  - remember (x ∩ y) as source eqn:source_eq in right.
    induction right; subst; try discriminate.
    + rewrite app_nil_r. now apply inter_right.
    + apply omega_right.
    + injection source_eq as first_eq second_eq. subst a b.
      destruct (inter_cuts x y eq_refl) as [cut_x _].
      eapply cut_x; eassumption.
    + injection source_eq as first_eq second_eq. subst a b.
      destruct (inter_cuts x y eq_refl) as [_ cut_y].
      eapply cut_y; eassumption.
    + apply inter_right; auto.
    + apply arrow_right. rewrite <- app_assoc. auto.
  - simpl. apply arrow_left; [assumption | now apply IHcodomain].
  - remember (x → y) as source eqn:source_eq in right.
    induction right as
      [u | u m | | | u v t m right_u IHu right_v IHv |
       input output argument target m argument_sub IHargument continuation IHcontinuation |
       u v t m continuation IHcontinuation]; subst; try discriminate.
    + rewrite app_nil_r. now apply arrow_right.
    + apply omega_right.
    + apply inter_right; auto.
    + injection source_eq as domain_eq codomain_eq. subst input output.
      destruct (arrow_cuts x y eq_refl) as [cut_x cut_y].
      (* Cut on the domain to replace the argument, then cut on the codomain. *)
      assert (replaced : s ❘ l · argument ⊦ y).
      { eapply sub_replace_argument with (p := l) (q := []).
        - intros z below_x. exact (cut_x _ _ [] [] argument_sub below_x).
        - exact left.
        - reflexivity. }
      change (s ❘ l ++ [argument] ++ m ⊦ target).
      rewrite app_assoc.
      exact (cut_y _ _ _ _ replaced continuation).
    + apply arrow_right. rewrite <- app_assoc. auto.
Qed.

Lemma sub_cut b : sub_cut_at b.
Proof.
  induction b; apply sub_cut_step; intros x y shape; try discriminate;
    injection shape as <- <-; split; assumption.
Qed.

Lemma bcd_to_sub a b : a ⩽ b -> a ❘ ⊦ b.
Proof.
  intro derivation.
  induction derivation.
  - apply identity.
  - exact (sub_cut IHderivation1 IHderivation2).
  - apply omega_right.
  - apply inter_left1, identity.
  - apply inter_left2, identity.
  - apply inter_right; apply identity.
  - apply inter_right.
    + now apply inter_left1.
    + now apply inter_left2.
  - apply arrow_right. now apply arrow_left.
  - apply arrow_right, inter_right.
    + apply inter_left1, arrow_left; apply identity.
    + apply inter_left2, arrow_left; apply identity.
  - apply arrow_right, omega_right.
  - contradiction.
Qed.

Lemma bcd_inter_intro a b c : a ⩽ b -> a ⩽ c -> a ⩽ b ∩ c.
Proof.
  intros below_b below_c.
  eapply bcd_trans.
  - apply bcd_inter_right.
  - now apply bcd_inter.
Qed.

Lemma bcd_context_omega l : Ω ⩽ fold_right arrow Ω l.
Proof.
  induction l as [|a l IH]; simpl.
  - apply bcd_identity.
  - eapply bcd_trans.
    + apply bcd_arrow_omega.
    + apply bcd_arrow; [apply bcd_omega_right | exact IH].
Qed.

Lemma bcd_context_inter l a b :
  fold_right arrow a l ∩ fold_right arrow b l ⩽ fold_right arrow (a ∩ b) l.
Proof.
  induction l as [|c l IH]; simpl.
  - apply bcd_identity.
  - eapply bcd_trans.
    + apply bcd_arrow_inter.
    + apply bcd_arrow; [apply bcd_identity | exact IH].
Qed.

(* Each context entry becomes an arrow domain, in list order. *)
Lemma sub_to_bcd l a b : a ❘ l ⊦ b -> a ⩽ fold_right arrow b l.
Proof.
  intro derivation.
  induction derivation; simpl in *.
  - apply bcd_identity.
  - eapply bcd_trans; [apply bcd_omega_right | apply bcd_context_omega].
  - eapply bcd_trans; [apply bcd_inter_left1 | exact IHderivation].
  - eapply bcd_trans; [apply bcd_inter_left2 | exact IHderivation].
  - eapply bcd_trans.
    + exact (bcd_inter_intro IHderivation1 IHderivation2).
    + apply bcd_context_inter.
  - now apply bcd_arrow.
  - rewrite fold_right_app in IHderivation. exact IHderivation.
Qed.

Theorem is_bcd_equiv a b : a ⩽ b <=> a ❘ ⊦ b.
Proof.
  split.
  - apply bcd_to_sub.
  - exact (@sub_to_bcd [] a b).
Qed.
