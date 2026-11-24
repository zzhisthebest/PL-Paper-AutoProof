From Stdlib Require Import List Permutation.
Import ListNotations.

(* simple types *)
Inductive sty : Type :=
  | satom (x : nat)   (* type variable *)
  | sarr (s t : sty). (* function type *)

(* type-annotated lambda-terms *)
Inductive tm : Type :=
  | var (n : nat)           (* term variable *)
  | app (M N : tm)          (* application *)
  | lam (t : sty) (M : tm). (* type-annotated abstraction *)

(* simply typed lambda-calculus *)
(* stlc Gamma M s means that in the type environment Gamma the term M is assigned the type s *)
Inductive stlc (Gamma : list sty) : tm -> sty -> Prop :=
  | stlc_var x t : nth_error Gamma x = Some t -> stlc Gamma (var x) t
  | stlc_app M N s t : stlc Gamma M (sarr s t) -> stlc Gamma N s -> stlc Gamma (app M N) t
  | stlc_lam M s t : stlc (cons s Gamma) M t -> stlc Gamma (lam (sarr s t) M) (sarr s t).

Inductive nity : Type :=
  | niatom (x : nat) : nity
  | niarr (u : list nity) (A : nity) : nity.

(* type environment *)
Notation environment := (list (list nity)).

(* ssim s A means non-idempotent type A collapses to simple type s *)
Inductive ssim : sty -> nity -> Prop :=
  | ssim_atom x : ssim (satom x) (niatom x)
  | ssim_arr s t A u B : Forall (ssim s) (cons A u) -> ssim t B -> ssim (sarr s t) (niarr (cons A u) B).


(* environment permutation *)
Notation sty_permutation Gammas Deltas :=
  (forall x, @Permutation nity
    (concat (map (fun Gamma => nth x Gamma nil) Gammas))
    (concat (map (fun Delta => nth x Delta nil) Deltas))).

(* non-idempotently typed lambda-calculus *)
(* nitlc Gamma M A means that in the type environment Gamma the term M is assigned the type A *)
Inductive nitlc (Gamma : environment) : tm -> nity -> Prop :=
  | nitlc_var t x A :
      ssim t A ->
      In A (nth x Gamma nil) ->
      nitlc Gamma (var x) A
  | nitlc_app Gamma' Deltas M N u A :
      sty_permutation [Gamma] (Gamma' :: Deltas) ->
      nitlc Gamma' M (niarr u A) ->
      Forall2 (fun B Delta => nitlc Delta N B) u Deltas ->
      nitlc Gamma (app M N) A
  | nitlc_lam t M u A :
      ssim t (niarr u A) ->
      nitlc (cons u Gamma) M A ->
      nitlc Gamma (lam t M) (niarr u A).

Definition ni_entry (s : sty) (P : nity -> Prop) (u : list nity) : Prop :=
  u <> [] /\ Forall (fun A => ssim s A /\ P A) u.

Lemma ni_entry_singleton s P A : ssim s A -> P A -> ni_entry s P [A].
Proof.
  intros HA HP. split; [discriminate |].
  constructor; [now split | constructor].
Qed.

Definition ni_apply (s : sty) (P Q : nity -> Prop) (B : nity) : Prop :=
  exists u, ni_entry s Q u /\ P (niarr u B).

(* At an arrow, applying the predicate to any reducible argument predicate
   must give a reducible result predicate. *)
Fixpoint ni_reducible (s : sty) (P : nity -> Prop) : Prop :=
  match s with
  | satom x => P (niatom x)
  | sarr a b => forall Q, ni_reducible a Q -> ni_reducible b (ni_apply a P Q)
  end.

Lemma ni_entry_arrow s t Q u B :
  ni_entry s Q u -> ssim t B -> ssim (sarr s t) (niarr u B).
Proof.
  intros [Hnonempty Hall] HB.
  destruct u as [|A u]; [contradiction |].
  constructor; [|exact HB].
  eapply Forall_impl; [|exact Hall].
  intros C [HC _]. exact HC.
Qed.

Lemma ni_reducible_monotone s (P Q : nity -> Prop) :
  (forall A, ssim s A -> P A -> Q A) ->
  ni_reducible s P -> ni_reducible s Q.
Proof.
  revert P Q.
  induction s as [x | s IHs t IHt]; intros P Q Himp HP.
  - simpl in *. apply Himp; [constructor | exact HP].
  - intros R HR.
    apply (IHt (ni_apply s P R)).
    + intros B HB [u [Hu Hfun]].
      exists u. split; [exact Hu |].
      apply Himp; [eapply ni_entry_arrow; eassumption | exact Hfun].
    + exact (HP R HR).
Qed.

Lemma ni_reducible_uniform s :
  ni_reducible s (ssim s) /\
  (forall P, ni_reducible s P -> exists A, ssim s A /\ P A).
Proof.
  induction s as [x | s [Hs Hs_witness] t [Ht Ht_witness]].
  - split.
    + simpl. constructor.
    + intros P HP. exists (niatom x). split; [constructor | exact HP].
  - split.
    + intros Q HQ.
      destruct (Hs_witness Q HQ) as [A [HA HQA]].
      assert (Hentry : ni_entry s Q [A]).
      { now apply ni_entry_singleton. }
      apply (ni_reducible_monotone t (ssim t)); [|exact Ht].
      intros B HB _.
      exists [A]. split; [exact Hentry |].
      eapply ni_entry_arrow; eassumption.
    + intros P HP.
      destruct (Ht_witness _ (HP (ssim s) Hs)) as [B [HB [u [Hu Hfun]]]].
      exists (niarr u B). split; [|exact Hfun].
      eapply ni_entry_arrow; eassumption.
Qed.

Definition ni_context (Xi : list (sty * (nity -> Prop))) (Gamma : environment) : Prop :=
  Forall2 (fun entry => ni_entry (fst entry) (snd entry)) Xi Gamma.

Lemma ni_variable_context Xi x t P A :
  Forall (fun entry => ni_reducible (fst entry) (snd entry)) Xi ->
  nth_error Xi x = Some (t, P) -> ssim t A -> P A ->
  exists Gamma, ni_context Xi Gamma /\ In A (nth x Gamma []).
Proof.
  intros HXi. revert x.
  induction HXi as [|[s Q] Xi HQ HXi IH]; intros [|x] Hnth HA HPA;
    try discriminate.
  - injection Hnth as <- <-.
    clear IH.
    assert (Htail : exists Gamma, ni_context Xi Gamma).
    { induction HXi as [|[r R] Xi HR HXi IH].
      - exists []. constructor.
      - destruct (proj2 (ni_reducible_uniform r) R HR) as [B [HB HRB]].
        destruct IH as [Gamma HG].
        exists ([B] :: Gamma). constructor; [|exact HG].
        now apply ni_entry_singleton. }
    destruct Htail as [Gamma HG].
    exists ([A] :: Gamma). split.
    + constructor; [|exact HG].
      now apply ni_entry_singleton.
    + simpl. now left.
  - destruct (IH x Hnth HA HPA) as [Gamma [HG Hin]].
    destruct (proj2 (ni_reducible_uniform s) Q HQ) as [B [HB HQB]].
    exists ([B] :: Gamma). split; [|exact Hin].
    constructor; [|exact HG].
    now apply ni_entry_singleton.
Qed.

Fixpoint ni_merge (Gamma Delta : environment) : environment :=
  match Gamma, Delta with
  | [], _ => Delta
  | _, [] => Gamma
  | u :: Gamma', v :: Delta' => (u ++ v) :: ni_merge Gamma' Delta'
  end.

Lemma ni_merge_nth Gamma Delta x :
  nth x (ni_merge Gamma Delta) [] = nth x Gamma [] ++ nth x Delta [].
Proof.
  revert Delta x.
  induction Gamma as [|u Gamma IH]; intros [|v Delta] [|x]; simpl;
    rewrite ?nth_nil, ?app_nil_r; auto.
Qed.

Lemma ni_merge_context Xi Gamma Delta :
  ni_context Xi Gamma -> ni_context Xi Delta -> ni_context Xi (ni_merge Gamma Delta).
Proof.
  intros HG. revert Delta.
  induction HG as [|[s P] u Xi Gamma [Hu Hall] HG IH]; intros Delta HD;
    inversion HD as [|entry v Xi' Delta' Hv HD']; subst; simpl.
  - constructor.
  - constructor.
    + destruct Hv as [_ Hv]. split.
      * intro Hempty. apply app_eq_nil in Hempty. tauto.
      * now apply Forall_app.
    + now apply IH.
Qed.

Lemma ni_collect_arguments Xi N u Gamma' :
  ni_context Xi Gamma' ->
  Forall (fun B => exists Delta, ni_context Xi Delta /\ nitlc Delta N B) u ->
  exists Gamma Deltas,
    ni_context Xi Gamma /\
    (forall x, nth x Gamma [] = nth x Gamma' [] ++
      concat (map (fun Delta => nth x Delta []) Deltas)) /\
    Forall2 (fun B Delta => nitlc Delta N B) u Deltas.
Proof.
  intros HG Hargs. revert Gamma' HG.
  induction Hargs as [|B u [Delta [HD HN]] Hargs IH]; intros Gamma' HG.
  - exists Gamma', []. split; [exact HG |].
    split; [intros x; simpl; now rewrite app_nil_r | constructor].
  - destruct (IH Delta HD) as [Theta [Deltas [HTheta [Hnth Htypes]]]].
    exists (ni_merge Gamma' Theta), (Delta :: Deltas).
    split; [now apply ni_merge_context |].
    split; [intro x; now rewrite ni_merge_nth, Hnth | now constructor].
Qed.

Lemma ni_typing_reducible Gamma0 M t :
  stlc Gamma0 M t ->
  forall Xi, map fst Xi = Gamma0 ->
  Forall (fun entry => ni_reducible (fst entry) (snd entry)) Xi ->
  ni_reducible t (fun A => exists Gamma, ni_context Xi Gamma /\ nitlc Gamma M A).
Proof.
  intros Htyping.
  induction Htyping as [Gamma0 x t Hnth | Gamma0 M N s t HM IHM HN IHN |
    Gamma0 M s t HM IH]; intros Xi Hmap HXi.
  - rewrite <- Hmap, nth_error_map in Hnth.
    destruct (nth_error Xi x) as [[s P]|] eqn:HX; simpl in Hnth; try discriminate.
    injection Hnth as ->.
    assert (HP : ni_reducible t P).
    { rewrite Forall_forall in HXi. apply (HXi (t, P)).
      exact (nth_error_In Xi x HX). }
    eapply ni_reducible_monotone; [|exact HP].
    intros A HA HPA.
    destruct (ni_variable_context Xi x t P A HXi HX HA HPA) as [Gamma [HG Hin]].
    exists Gamma. split; [exact HG |]. exact (nitlc_var Gamma t x A HA Hin).
  - specialize (IHM Xi Hmap HXi). specialize (IHN Xi Hmap HXi).
    eapply ni_reducible_monotone; [|exact (IHM _ IHN)].
    intros A _ [u [Hu [Gamma' [HG' HM']]]].
    destruct Hu as [_ Hargs].
    assert (Hall : Forall (fun B => exists Delta, ni_context Xi Delta /\ nitlc Delta N B) u).
    { eapply Forall_impl; [|exact Hargs]. intros B [_ HB]. exact HB. }
    destruct (ni_collect_arguments Xi N u Gamma' HG' Hall)
      as [Gamma [Deltas [HG [Hnth Htypes]]]].
    exists Gamma. split; [exact HG |].
    eapply nitlc_app; [|exact HM' |exact Htypes].
    intro x. simpl. rewrite app_nil_r, Hnth. reflexivity.
  - intros Q HQ.
    assert (Hbody : Forall (fun entry => ni_reducible (fst entry) (snd entry)) ((s, Q) :: Xi)).
    { constructor; assumption. }
    specialize (IH ((s, Q) :: Xi) ltac:(now simpl; rewrite Hmap) Hbody).
    eapply ni_reducible_monotone; [|exact IH].
    intros B HB [Delta [HD HM']].
    inversion HD as [|entry u Xi' Gamma Hu HG]; subst.
    exists u. split; [exact Hu |].
    exists Gamma. split; [exact HG |].
    apply nitlc_lam; [eapply ni_entry_arrow; eassumption | exact HM'].
Qed.

Theorem nitlc_type_inference M Gamma0 t : stlc Gamma0 M t ->
  exists Gamma A,
    nitlc Gamma M A /\
    Forall2 (fun s u => u <> [] /\ Forall (ssim s) u) Gamma0 Gamma /\
    ssim t A.
Proof.
  intros HM.
  set (Xi := map (fun s => (s, ssim s)) Gamma0).
  assert (Hmap : map fst Xi = Gamma0).
  { unfold Xi. rewrite map_map. apply map_id. }
  assert (HXi : Forall (fun entry => ni_reducible (fst entry) (snd entry)) Xi).
  { unfold Xi. apply Forall_map, Forall_forall.
    intros s _. exact (proj1 (ni_reducible_uniform s)). }
  destruct (proj2 (ni_reducible_uniform t) _ (ni_typing_reducible Gamma0 M t HM Xi Hmap HXi))
    as [A [HA [Gamma [HG Htyped]]]].
  exists Gamma, A. split; [exact Htyped |]. split; [|exact HA].
  rewrite <- Hmap. clear Hmap HXi Htyped. unfold ni_context in HG.
  induction HG as [|[s P] u Xi' Gamma' [Hu Hall] HG IH]; simpl; constructor.
  - split; [exact Hu |].
    eapply Forall_impl; [|exact Hall]. intros B [HB _]. exact HB.
  - exact IH.
Qed.
