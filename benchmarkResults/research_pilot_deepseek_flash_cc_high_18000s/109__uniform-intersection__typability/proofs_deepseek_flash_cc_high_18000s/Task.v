From Stdlib Require Import List Permutation.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.
From Stdlib Require Import Wellfounded.Inverse_Image.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Psatz.
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

(* Basic shape inversion for the collapse relation. *)

Lemma ssim_atom_inv x A : ssim (satom x) A -> A = niatom x.
Proof.
  intros H. inversion H. reflexivity.
Qed.

Lemma ssim_arr_inv s t A :
  ssim (sarr s t) A ->
  exists u B, A = niarr u B /\ u <> [] /\ Forall (ssim s) u /\ ssim t B.
Proof.
  intros H. inversion H as [x | s1 t1 A0 u B Hfa Hssim].
  exists (A0 :: u), B. split.
  - reflexivity.
  - split.
    + intro Hnil; discriminate Hnil.
    + split; assumption.
Qed.

(* The identity lambda is typable at the "self" type determined by any
   singleton argument list.  This exercises the lambda and variable rules
   with a non-thin argument list and is a basic building block for the
   principal/inflated typings needed by the target. *)

Lemma nitlc_lam_id A s :
  ssim s A -> nitlc [] (lam (sarr s s) (var 0)) (niarr [A] A).
Proof.
  intro H.
  apply nitlc_lam with (t := sarr s s) (u := [A]) (A := A).
  - apply (ssim_arr s s A [] A).
    + constructor.
      * exact H.
      * constructor.
    + exact H.
  - simpl. apply nitlc_var with (t := s).
    + exact H.
    + simpl. left. reflexivity.
Qed.

(* Support-preserving inflation of non-idempotent types: each element of an
   argument list is replaced by a non-empty block of inflated elements.
   This is the order intended for the saturation/retargeting step. *)

Inductive nle : nity -> nity -> Prop :=
| nle_atom x : nle (niatom x) (niatom x)
| nle_arr u A v B : nle_list u v -> nle A B -> nle (niarr u A) (niarr v B)
with nle_list : list nity -> list nity -> Prop :=
| nle_list_nil : nle_list [] []
| nle_list_cons a u v v' :
    v <> [] -> Forall (nle a) v -> nle_list u v' -> nle_list (a :: u) (v ++ v').

(* Structural size of a non-idempotent type and of its argument lists.
   The list size counts a separator per element, so every element and every
   tail has strictly smaller size. *)

Fixpoint nsize (A : nity) : nat :=
  match A with
  | niatom _ => 1
  | niarr u B =>
      1 + (fix go (l : list nity) : nat :=
             match l with
             | [] => 0
             | C :: l' => 1 + nsize C + go l'
             end) u
        + nsize B
  end.

Definition lsize (u : list nity) : nat :=
  (fix go (l : list nity) : nat :=
     match l with
     | [] => 0
     | C :: l' => 1 + nsize C + go l'
     end) u.

Lemma nsize_niarr u B : nsize (niarr u B) = 1 + lsize u + nsize B.
Proof. reflexivity. Qed.

Lemma lsize_cons a u : lsize (a :: u) = 1 + nsize a + lsize u.
Proof. reflexivity. Qed.

Lemma nsize_pos A : 0 < nsize A.
Proof. destruct A as [x | u B]; simpl; lia. Qed.

Lemma In_nsize_lt_lsize a u : In a u -> nsize a < lsize u.
Proof.
  intros H. induction u as [| b u' IH].
  - destruct H.
  - simpl in H. rewrite lsize_cons. destruct H as [-> | H].
    + lia.
    + specialize (IH H). lia.
Qed.

Definition msize (x : nity + list nity) : nat :=
  match x with
  | inl A => nsize A
  | inr u => lsize u
  end.

Lemma nle_refl_all :
  forall x : nity + list nity,
    match x with inl A => nle A A | inr u => nle_list u u end.
Proof.
  refine (well_founded_ind
            (@wf_inverse_image (nity + list nity) nat lt msize lt_wf)
            (fun x => match x with inl A => nle A A | inr u => nle_list u u end)
            _).
  intros [A | u] IH.
  - destruct A as [x | u B].
    + constructor.
    + constructor.
      * apply (IH (inr u)). change (lsize u < nsize (niarr u B)).
        rewrite nsize_niarr. pose proof (nsize_pos B). lia.
      * apply (IH (inl B)). change (nsize B < nsize (niarr u B)).
        rewrite nsize_niarr. lia.
  - destruct u as [| a u'].
    + constructor.
    + apply (nle_list_cons a u' [a] u').
      * discriminate.
      * constructor.
        -- apply (IH (inl a)). change (nsize a < lsize (a :: u')).
           rewrite lsize_cons. lia.
        -- constructor.
      * apply (IH (inr u')). change (lsize u' < lsize (a :: u')).
        rewrite lsize_cons. lia.
Qed.

Lemma nle_refl A : nle A A.
Proof. apply (nle_refl_all (inl A)). Qed.

Lemma nle_list_refl u : nle_list u u.
Proof. apply (nle_refl_all (inr u)). Qed.

(* Splitting an nle_list inflation along a decomposition of the source
   list.  This matches the environment decomposition in nitlc_app. *)
Lemma nle_list_app_split :
  forall u1 u2 v, nle_list (u1 ++ u2) v ->
  exists v1 v2, v = v1 ++ v2 /\ nle_list u1 v1 /\ nle_list u2 v2.
Proof.
  induction u1 as [| a u1 IH]; intros u2 v H.
  - simpl in H. exists [], v. split.
    + rewrite app_nil_l. reflexivity.
    + split; [constructor | exact H].
  - simpl in H.
    inversion H as [| a0 u0 vblock vtail Hne Hfa Htail]; subst.
    destruct (IH u2 vtail Htail) as [v1' [v2 [Heq [Hl1 Hl2]]]].
    exists (vblock ++ v1'), v2. split.
    + rewrite Heq. rewrite app_assoc. reflexivity.
    + split.
      * apply (nle_list_cons a u1 vblock v1' Hne Hfa Hl1).
      * exact Hl2.
Qed.

Lemma nle_list_nonempty u v : nle_list u v -> u <> [] -> v <> [].
Proof.
  intros H. induction H as [| a u vblock vtail Hne Hfa Htail IH].
  - intro Hu. exact Hu.
  - intro Hu. intro Hv. apply app_eq_nil in Hv. destruct Hv as [E _].
    exact (Hne E).
Qed.

Lemma nle_ssim_all :
  forall x : nity + list nity,
    match x with
    | inl A => forall B, nle A B -> forall s, ssim s A -> ssim s B
    | inr u => forall v, nle_list u v ->
               forall s, Forall (ssim s) u -> Forall (ssim s) v
    end.
Proof.
  refine (well_founded_ind
            (@wf_inverse_image (nity + list nity) nat lt msize lt_wf)
            (fun x => match x with
                      | inl A => forall B, nle A B -> forall s, ssim s A -> ssim s B
                      | inr u => forall v, nle_list u v ->
                                 forall s, Forall (ssim s) u -> Forall (ssim s) v
                      end)
            _).
  intros [A | u] IH.
  - intros B Hnle s Hssim.
    destruct Hnle as [x | u_arr A_arr v_arr B_arr Hlist Hnle].
    + inversion Hssim. constructor.
    + inversion Hssim as [x | s1 s2 A0 u0 Bss Hfa Hssim2]; subst.
      destruct v_arr as [| B0 vtail].
      * exfalso.
        assert (Hne : A0 :: u0 <> []) by (intro E; discriminate E).
        exact (nle_list_nonempty (A0 :: u0) [] Hlist Hne eq_refl).
      * apply ssim_arr.
        -- apply (IH (inr (A0 :: u0))).
           ++ change (lsize (A0 :: u0) < nsize (niarr (A0 :: u0) A_arr)).
              rewrite nsize_niarr. pose proof (nsize_pos A_arr). lia.
           ++ exact Hlist.
           ++ exact Hfa.
        -- apply (IH (inl A_arr)).
           ++ change (nsize A_arr < nsize (niarr (A0 :: u0) A_arr)).
              rewrite nsize_niarr. lia.
           ++ exact Hnle.
           ++ exact Hssim2.
  - intros v Hlist s Hfa.
    destruct Hlist as [| a u' vblock vtail Hne Hfa_block Hlist_tail].
    + constructor.
    + apply Forall_app. split.
      * apply (proj2 (Forall_forall (ssim s) vblock)). intros b Hb.
        apply (IH (inl a)).
        -- change (nsize a < lsize (a :: u')). rewrite lsize_cons. lia.
        -- exact (proj1 (Forall_forall (nle a) vblock) Hfa_block b Hb).
        -- exact (Forall_inv Hfa).
      * apply (IH (inr u')).
        -- change (lsize u' < lsize (a :: u')). rewrite lsize_cons. lia.
        -- exact Hlist_tail.
        -- apply (Forall_inv_tail Hfa).
Qed.

Lemma nle_ssim A B s : nle A B -> ssim s A -> ssim s B.
Proof. intros Hn Hs. exact (nle_ssim_all (inl A) B Hn s Hs). Qed.

Lemma nle_list_ssim u v s :
  nle_list u v -> Forall (ssim s) u -> Forall (ssim s) v.
Proof. intros Hn Hs. exact (nle_ssim_all (inr u) v Hn s Hs). Qed.

(* Cover-style inflation: every new element is an inflation of some old
   element, and every old element is dominated by some new element.  This
   is the flexible form needed for directedness/joining. *)

Inductive nle2 : nity -> nity -> Prop :=
| nle2_atom x : nle2 (niatom x) (niatom x)
| nle2_arr u A v B :
    (forall b, In b v -> exists a, In a u /\ nle2 a b) ->
    (forall a, In a u -> exists b, In b v /\ nle2 a b) ->
    nle2 A B ->
    nle2 (niarr u A) (niarr v B).

Lemma nle2_refl : forall A, nle2 A A.
Proof.
  refine (well_founded_ind
            (@wf_inverse_image nity nat lt nsize lt_wf)
            (fun A => nle2 A A) _).
  intros A IH. destruct A as [x | u B].
  - constructor.
  - constructor.
    + intros b Hb. exists b. split; [exact Hb |].
      apply IH. change (nsize b < nsize (niarr u B)).
      rewrite nsize_niarr.
      pose proof (In_nsize_lt_lsize b u Hb). pose proof (nsize_pos B). lia.
    + intros a Ha. exists a. split; [exact Ha |].
      apply IH. change (nsize a < nsize (niarr u B)).
      rewrite nsize_niarr.
      pose proof (In_nsize_lt_lsize a u Ha). pose proof (nsize_pos B). lia.
    + apply IH. change (nsize B < nsize (niarr u B)).
      rewrite nsize_niarr. pose proof (nsize_pos B). lia.
Qed.

Lemma nle2_trans : forall A B C, nle2 A B -> nle2 B C -> nle2 A C.
Proof.
  refine (well_founded_ind
            (@wf_inverse_image nity nat lt nsize lt_wf)
            (fun A => forall B C, nle2 A B -> nle2 B C -> nle2 A C) _).
  intros A IH B C HAB HBC.
  destruct HAB as [x | u A2 v B2 HcovAB1 HcovAB2 HleAB].
  - inversion HBC. constructor.
  - inversion HBC as [y | v' B2' w C2' HcovBC1 HcovBC2 HleBC]; subst.
    constructor.
    + intros c Hc. destruct (HcovBC1 c Hc) as [b [Hb Hbc]].
      destruct (HcovAB1 b Hb) as [a [Ha Hab]].
      exists a. split; [exact Ha |].
      assert (Hmeas : nsize a < nsize (niarr u A2)).
      { rewrite nsize_niarr. pose proof (In_nsize_lt_lsize a u Ha).
        pose proof (nsize_pos A2). lia. }
      apply (IH a Hmeas b).
      * exact Hab.
      * exact Hbc.
    + intros a Ha. destruct (HcovAB2 a Ha) as [b [Hb Hab]].
      destruct (HcovBC2 b Hb) as [c [Hc Hbc]].
      exists c. split; [exact Hc |].
      assert (Hmeas : nsize a < nsize (niarr u A2)).
      { rewrite nsize_niarr. pose proof (In_nsize_lt_lsize a u Ha).
        pose proof (nsize_pos A2). lia. }
      apply (IH a Hmeas b).
      * exact Hab.
      * exact Hbc.
    + assert (Hmeas : nsize A2 < nsize (niarr u A2)).
      { rewrite nsize_niarr. pose proof (nsize_pos A2). lia. }
      apply (IH A2 Hmeas B2).
      * exact HleAB.
      * exact HleBC.
Qed.

Lemma nle2_ssim : forall A B s, nle2 A B -> ssim s A -> ssim s B.
Proof.
  refine (well_founded_ind
            (@wf_inverse_image nity nat lt nsize lt_wf)
            (fun A => forall B s, nle2 A B -> ssim s A -> ssim s B) _).
  intros A IH B s Hnle Hssim.
  destruct Hnle as [x | u_arr A_arr v_arr B_arr Hcov1 Hcov2 Hnle].
  - inversion Hssim. constructor.
  - inversion Hssim as [x | s1 s2 A0 u0 Bss Hfa Hssim2]; subst.
    destruct v_arr as [| B0 vtail].
    + destruct (Hcov2 A0 (or_introl eq_refl)) as [b [Hin _]]. destruct Hin.
    + apply ssim_arr.
      * apply (proj2 (Forall_forall (ssim s1) (B0 :: vtail))).
        intros b Hb.
        destruct (Hcov1 b Hb) as [a [Hina Hleab]].
        apply (IH a).
        -- change (nsize a < nsize (niarr (A0 :: u0) A_arr)).
           rewrite nsize_niarr.
           pose proof (In_nsize_lt_lsize a (A0 :: u0) Hina).
           pose proof (nsize_pos A_arr). lia.
        -- exact Hleab.
        -- exact (proj1 (Forall_forall (ssim s1) (A0 :: u0)) Hfa a Hina).
      * apply (IH A_arr).
        -- change (nsize A_arr < nsize (niarr (A0 :: u0) A_arr)).
           rewrite nsize_niarr. pose proof (nsize_pos A_arr). lia.
        -- exact Hnle.
        -- exact Hssim2.
Qed.

(* Constructive finite choice for Forall2, and membership projections. *)

Lemma Forall2_exists_gen :
  forall (A B : Type) (l : list A) (P : A -> B -> Prop),
    (forall x, In x l -> exists y, P x y) ->
    exists l', Forall2 P l l'.
Proof.
  intros A B l P H. induction l as [| a l' IH].
  - exists []. constructor.
  - destruct (H a (or_introl eq_refl)) as [y Hy].
    destruct (IH (fun x Hx => H x (or_intror Hx))) as [l'' Hl''].
    exists (y :: l''). constructor; assumption.
Qed.

Lemma Forall2_in_right :
  forall {A B : Type} (P : A -> B -> Prop) l l' x,
    Forall2 P l l' -> In x l' -> exists y, In y l /\ P y x.
Proof.
  intros A B P l. induction l as [| a l' IH]; intros l'' x H Hx.
  - inversion H; subst; destruct Hx.
  - destruct l'' as [| b l''].
    + inversion H.
    + inversion H as [| ? ? ? ? HPa Hrest]; subst.
      destruct Hx as [-> | Hx].
      * exists a. split; [left; reflexivity | exact HPa].
      * destruct (IH l'' x Hrest Hx) as [y [Hy Hpy]].
        exists y. split; [right; exact Hy | exact Hpy].
Qed.

Lemma Forall2_in_left :
  forall {A B : Type} (P : A -> B -> Prop) l l' x,
    Forall2 P l l' -> In x l -> exists y, In y l' /\ P x y.
Proof.
  intros A B P l. induction l as [| a l' IH]; intros l'' x H Hx.
  - destruct Hx.
  - destruct l'' as [| b l''].
    + inversion H.
    + inversion H as [| ? ? ? ? HPa Hrest]; subst.
      destruct Hx as [-> | Hx].
      * exists b. split; [left; reflexivity | exact HPa].
      * destruct (IH l'' x Hrest Hx) as [y [Hy Hpy]].
        exists y. split; [right; exact Hy | exact Hpy].
Qed.

(* Directedness: any two types of the same simple type have a common
   inflation.  The common argument list is the list of pairwise joins. *)

Lemma nle2_directed :
  forall s A B, ssim s A -> ssim s B -> exists C, nle2 A C /\ nle2 B C.
Proof.
  induction s as [x | s1 IHs1 s2 IHs2].
  - intros A B HA HB. inversion HA; inversion HB; subst.
    exists (niatom x). split; constructor.
  - intros A B HA HB.
    inversion HA as [x0 | sA1 sA2 A0 u0 Bss Hfa HssimA]; subst.
    inversion HB as [x0 | sB1 sB2 B0 v0 Css Hfb HssimB]; subst.
    destruct (IHs2 Bss Css HssimA HssimB) as [C2 [HleA2 HleB2]].
    assert (Hrows : forall a, In a (A0 :: u0) ->
              exists L, Forall2 (fun b C => nle2 a C /\ nle2 b C)
                                (B0 :: v0) L).
    { intros a Ha.
      apply (Forall2_exists_gen nity nity (B0 :: v0)).
      intros b Hb.
      destruct (IHs1 a b
                  (proj1 (Forall_forall (ssim s1) (A0 :: u0)) Hfa a Ha)
                  (proj1 (Forall_forall (ssim s1) (B0 :: v0)) Hfb b Hb))
        as [C [Hle_a Hle_b]].
      exists C. split; assumption. }
    destruct (Forall2_exists_gen nity (list nity) (A0 :: u0)
                (fun a L => Forall2 (fun b C => nle2 a C /\ nle2 b C)
                                    (B0 :: v0) L) Hrows) as [Ls HLs].
    exists (niarr (concat Ls) C2). split.
    + constructor.
      * intros c Hc.
        rewrite in_concat in Hc. destruct Hc as [L [HinL HcL]].
        destruct (Forall2_in_right
                    (fun a L => Forall2 (fun b C => nle2 a C /\ nle2 b C)
                                        (B0 :: v0) L)
                    (A0 :: u0) Ls L HLs HinL) as [a [Hina HQ]].
        destruct (Forall2_in_right (fun b C => nle2 a C /\ nle2 b C)
                    (B0 :: v0) L c HQ HcL) as [b [Hinb [Hle_a Hle_b]]].
        exists a. split; assumption.
      * intros a Ha.
        destruct (Forall2_in_left
                    (fun a L => Forall2 (fun b C => nle2 a C /\ nle2 b C)
                                        (B0 :: v0) L)
                    (A0 :: u0) Ls a HLs Ha) as [L [HinL HQ]].
        destruct (Forall2_in_left (fun b C => nle2 a C /\ nle2 b C)
                    (B0 :: v0) L B0 HQ (or_introl eq_refl))
          as [c [Hinc [Hle_a Hle_b]]].
        exists c. split.
        -- rewrite in_concat. exists L. split; assumption.
        -- exact Hle_a.
      * exact HleA2.
    + constructor.
      * intros c Hc.
        rewrite in_concat in Hc. destruct Hc as [L [HinL HcL]].
        destruct (Forall2_in_right
                    (fun a L => Forall2 (fun b C => nle2 a C /\ nle2 b C)
                                        (B0 :: v0) L)
                    (A0 :: u0) Ls L HLs HinL) as [a [Hina HQ]].
        destruct (Forall2_in_right (fun b C => nle2 a C /\ nle2 b C)
                    (B0 :: v0) L c HQ HcL) as [b [Hinb [Hle_a Hle_b]]].
        exists b. split; assumption.
      * intros b Hb.
        destruct (Forall2_in_left
                    (fun a L => Forall2 (fun b C => nle2 a C /\ nle2 b C)
                                        (B0 :: v0) L)
                    (A0 :: u0) Ls A0 HLs (or_introl eq_refl))
          as [L [HinL HQ]].
        destruct (Forall2_in_left (fun b C => nle2 A0 C /\ nle2 b C)
                    (B0 :: v0) L b HQ Hb) as [c [Hinc [Hle_a Hle_b]]].
        exists c. split.
        -- rewrite in_concat. exists L. split; assumption.
        -- exact Hle_b.
      * exact HleB2.
Qed.

(* Deterministic directed join of two nity types of the same simple type. *)
Fixpoint jn (s : sty) (A B : nity) {struct s} : nity :=
  match s with
  | satom x => niatom x
  | sarr s1 s2 =>
      match A, B with
      | niarr u A2, niarr v B2 =>
          niarr (concat (map (fun a => map (fun b => jn s1 a b) v) u))
                (jn s2 A2 B2)
      | _, _ => niatom 0
      end
  end.

Lemma in_concat_map_map_iff :
  forall (u v : list nity) (f : nity -> nity -> nity) (w : nity),
    In w (concat (map (fun a => map (fun b => f a b) v) u)) <->
    exists a b, In a u /\ In b v /\ f a b = w.
Proof.
  induction u as [| a u IH]; intros v f w; simpl.
  - split.
    + intros H. destruct H.
    + intros [a [b [Ha _]]]. destruct Ha.
  - rewrite in_app_iff, in_map_iff. split.
    + intros [H | H].
      * destruct H as [b [Heq Hb]].
        exists a, b. split; [left; reflexivity |]. split; [exact Hb | exact Heq].
      * apply IH in H. destruct H as [a' [b [Ha' [Hb Heq]]]].
        exists a', b. split; [right; exact Ha' |]. split; [exact Hb | exact Heq].
    + intros [a' [b [Ha' [Hb Heq]]]]. destruct Ha' as [HeqA | Ha'].
      * subst a'. left. exists b. split; [exact Heq | exact Hb].
      * right. apply IH. exists a', b. split; [exact Ha' |]. split; [exact Hb | exact Heq].
Qed.

Lemma concat_map_map_nonempty :
  forall (u v : list nity) (f : nity -> nity -> nity),
    u <> [] -> v <> [] ->
    concat (map (fun a => map (fun b => f a b) v) u) <> [].
Proof.
  intros u v f Hu Hv.
  destruct u as [| a u'].
  - exfalso. exact (Hu eq_refl).
  - destruct v as [| b v'].
    + exfalso. exact (Hv eq_refl).
    + assert (Hin : In (f a b) (concat (map (fun a => map (fun b => f a b) (b :: v')) (a :: u')))).
      { apply (proj2 (in_concat_map_map_iff (a :: u') (b :: v') f (f a b))).
        exists a, b. split; [left; reflexivity |]. split; [left; reflexivity | reflexivity]. }
      intro H. rewrite H in Hin. destruct Hin.
Qed.

Lemma jn_ssim : forall s A B, ssim s A -> ssim s B -> ssim s (jn s A B).
Proof.
  induction s as [x | s1 IHs1 s2 IHs2]; intros A B HA HB.
  - inversion HA; inversion HB; subst. simpl. constructor.
  - inversion HA as [x0 | sA1 sA2 A0 u0 Bss Hfa HssimA]; subst.
    inversion HB as [x0 | sB1 sB2 B0 v0 Css Hfb HssimB]; subst.
    simpl.
    remember (concat (map (fun a => map (fun b => jn s1 a b) (B0 :: v0))
                          (A0 :: u0))) as L eqn:EL.
    assert (Hne : L <> []).
    { rewrite EL. apply concat_map_map_nonempty; discriminate. }
    assert (HfaL : Forall (ssim s1) L).
    { rewrite EL. apply Forall_forall. intros e He.
      apply (proj1 (in_concat_map_map_iff (A0 :: u0) (B0 :: v0)
                    (fun a b => jn s1 a b) e)) in He.
      destruct He as [a [b [Ha [Hb Heq]]]]. subst e.
      apply IHs1.
      - exact (proj1 (Forall_forall (ssim s1) (A0 :: u0)) Hfa a Ha).
      - exact (proj1 (Forall_forall (ssim s1) (B0 :: v0)) Hfb b Hb). }
    destruct L as [| h t].
    { exfalso. exact (Hne eq_refl). }
    apply ssim_arr.
    + rewrite EL in HfaL. exact HfaL.
    + apply IHs2; assumption.
Qed.

Lemma jn_nle2_left : forall s A B, ssim s A -> ssim s B -> nle2 A (jn s A B).
Proof.
  induction s as [x | s1 IHs1 s2 IHs2]; intros A B HA HB.
  - inversion HA; inversion HB; subst. simpl. constructor.
  - inversion HA as [x0 | sA1 sA2 A0 u0 Bss Hfa HssimA]; subst.
    inversion HB as [x0 | sB1 sB2 B0 v0 Css Hfb HssimB]; subst.
    simpl. apply nle2_arr.
    + intros w Hw.
      apply (proj1 (in_concat_map_map_iff (A0 :: u0) (B0 :: v0)
                    (fun a b => jn s1 a b) w)) in Hw.
      destruct Hw as [a [b [Ha [Hb Heq]]]]. subst w.
      exists a. split; [exact Ha |].
      apply IHs1.
      * exact (proj1 (Forall_forall (ssim s1) (A0 :: u0)) Hfa a Ha).
      * exact (proj1 (Forall_forall (ssim s1) (B0 :: v0)) Hfb b Hb).
    + intros a Ha.
      exists (jn s1 a B0). split.
      * apply (proj2 (in_concat_map_map_iff (A0 :: u0) (B0 :: v0)
                      (fun a b => jn s1 a b) (jn s1 a B0))).
        exists a, B0. split; [exact Ha |]. split; [left; reflexivity | reflexivity].
      * apply IHs1.
        -- exact (proj1 (Forall_forall (ssim s1) (A0 :: u0)) Hfa a Ha).
        -- exact (Forall_inv Hfb).
    + apply IHs2; assumption.
Qed.

Lemma jn_nle2_right : forall s A B, ssim s A -> ssim s B -> nle2 B (jn s A B).
Proof.
  induction s as [x | s1 IHs1 s2 IHs2]; intros A B HA HB.
  - inversion HA; inversion HB; subst. simpl. constructor.
  - inversion HA as [x0 | sA1 sA2 A0 u0 Bss Hfa HssimA]; subst.
    inversion HB as [x0 | sB1 sB2 B0 v0 Css Hfb HssimB]; subst.
    simpl. apply nle2_arr.
    + intros w Hw.
      apply (proj1 (in_concat_map_map_iff (A0 :: u0) (B0 :: v0)
                    (fun a b => jn s1 a b) w)) in Hw.
      destruct Hw as [a [b [Ha [Hb Heq]]]]. subst w.
      exists b. split; [exact Hb |].
      apply IHs1.
      * exact (proj1 (Forall_forall (ssim s1) (A0 :: u0)) Hfa a Ha).
      * exact (proj1 (Forall_forall (ssim s1) (B0 :: v0)) Hfb b Hb).
    + intros b Hb.
      exists (jn s1 A0 b). split.
      * apply (proj2 (in_concat_map_map_iff (A0 :: u0) (B0 :: v0)
                      (fun a b => jn s1 a b) (jn s1 A0 b))).
        exists A0, b. split; [left; reflexivity |]. split; [exact Hb | reflexivity].
      * apply IHs1.
        -- exact (Forall_inv Hfa).
        -- exact (proj1 (Forall_forall (ssim s1) (B0 :: v0)) Hfb b Hb).
    + apply IHs2; assumption.
Qed.

Definition incl (l L : list nity) : Prop :=
  exists L1 L2, Permutation L (L1 ++ l ++ L2).

Lemma incl_refl L : incl L L.
Proof. exists [], []. simpl. rewrite app_nil_r. apply Permutation_refl. Qed.

Lemma perm_blocks (A:Type) (a b X:list A) :
  Permutation (a ++ b ++ X) (b ++ a ++ X).
Proof.
  apply Permutation_trans with (l' := (b ++ X) ++ a).
  - apply Permutation_app_comm.
  - rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
Qed.

Lemma perm4 (A:Type) (a b c d:list A) :
  Permutation (a ++ b ++ c ++ d) (b ++ a ++ d ++ c).
Proof.
  eapply Permutation_trans with (l' := b ++ a ++ c ++ d).
  - apply perm_blocks.
  - apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm.
Qed.

Lemma incl_split : forall L R Rs,
  incl (R ++ concat Rs) L ->
  exists Ls, Permutation L (concat Ls) /\ Forall2 incl (R :: Rs) Ls.
Proof.
  intros L R Rs. revert L R. induction Rs as [| R' Rs IH]; intros L R H.
  - rewrite app_nil_r in H.
    exists [L]. split.
    + simpl. rewrite app_nil_r. apply Permutation_refl.
    + constructor; [exact H | constructor].
  - simpl in H. destruct H as [L1 [L2 HP]].
    set (L0 := R ++ L1 ++ L2).
    assert (HP0 : Permutation L (L0 ++ (R' ++ concat Rs))).
    { unfold L0. eapply Permutation_trans.
      - exact HP.
      - eapply Permutation_trans with (l' := R ++ L1 ++ L2 ++ (R' ++ concat Rs)).
        + rewrite <- app_assoc. apply perm4.
        + rewrite <- app_assoc. rewrite <- app_assoc. apply Permutation_refl. }
    destruct (IH (R' ++ concat Rs) R' (incl_refl (R' ++ concat Rs))) as [Ls [HP2 Hfa2]].
    exists (L0 :: Ls). simpl. split.
    + eapply Permutation_trans.
      * exact HP0.
      * apply Permutation_app_head. exact HP2.
    + constructor.
      * unfold L0. exists [], (L1 ++ L2). simpl. apply Permutation_refl.
      * exact Hfa2.
Qed.

Definition J0 (s : sty) (u v : list nity) : list nity :=
  concat (map (fun a => map (fun b => jn s a b) v) u).

Lemma J0_app_l : forall s u1 u2 v,
  J0 s (u1 ++ u2) v = J0 s u1 v ++ J0 s u2 v.
Proof. intros. unfold J0. rewrite map_app, concat_app. reflexivity. Qed.

Lemma perm_mid (A : Type) (a b c d : list A) :
  Permutation ((a ++ b) ++ (c ++ d)) ((a ++ c) ++ (b ++ d)).
Proof.
  apply Permutation_trans with (l' := a ++ (c ++ (b ++ d))).
  - rewrite <- app_assoc. apply Permutation_app_head. apply perm_blocks.
  - rewrite <- app_assoc. apply Permutation_refl.
Qed.

Lemma J0_app_r : forall s u v1 v2,
  Permutation (J0 s u (v1 ++ v2)) (J0 s u v1 ++ J0 s u v2).
Proof.
  intros s u. induction u as [| a u IH]; intros v1 v2.
  - unfold J0. simpl. apply Permutation_refl.
  - unfold J0. simpl.
    fold (J0 s u (v1 ++ v2)). fold (J0 s u v1). fold (J0 s u v2).
    rewrite map_app.
    eapply Permutation_trans.
    + apply Permutation_app; [apply Permutation_refl | apply IH].
    + apply perm_mid.
Qed.

Lemma J0_in : forall s u v a b,
  In a u -> In b v -> In (jn s a b) (J0 s u v).
Proof.
  intros s u v a b Ha Hb. unfold J0.
  apply (proj2 (in_concat_map_map_iff u v (fun a b => jn s a b) (jn s a b))).
  exists a, b. split; [exact Ha | split; [exact Hb | reflexivity]].
Qed.

Lemma incl_in : forall l L x, incl l L -> In x l -> In x L.
Proof.
  intros l L x [L1 [L2 HP]] Hx.
  apply (Permutation_in x (Permutation_sym HP)).
  apply in_or_app. right. apply in_or_app. left. exact Hx.
Qed.

Definition Jinv (Gamma0 : list sty) (G1 G2 E : environment) : Prop :=
  forall x,
    incl (J0 (nth x Gamma0 (satom 0)) (nth x G1 nil) (nth x G2 nil))
         (nth x E nil).

Lemma J0_nil_l : forall s v, J0 s [] v = [].
Proof. reflexivity. Qed.

Lemma J0_nil_r : forall s u, J0 s u [] = [].
Proof.
  intros s u. induction u as [| a u IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.

Lemma Jinv_cons : forall s Gamma0 u v G1 G2 E,
  Jinv Gamma0 G1 G2 E ->
  Jinv (cons s Gamma0) (cons u G1) (cons v G2) (cons (J0 s u v) E).
Proof.
  intros s Gamma0 u v G1 G2 E H x. destruct x as [| x'].
  - simpl. apply incl_refl.
  - simpl. apply H.
Qed.

Lemma incl_trans : forall l1 l2 L, incl l1 l2 -> incl l2 L -> incl l1 L.
Proof.
  intros l1 l2 L [A1 [A2 HP1]] [B1 [B2 HP2]].
  exists (B1 ++ A1), (A2 ++ B2).
  eapply Permutation_trans.
  - exact HP2.
  - eapply Permutation_trans with (l' := B1 ++ (A1 ++ l1 ++ A2) ++ B2).
    + apply Permutation_app_head. apply Permutation_app_tail. exact HP1.
    + repeat rewrite app_assoc. apply Permutation_refl.
Qed.

Lemma Forall2_nth : forall (A B : Type) (P : A -> B -> Prop) l1 l2,
  Forall2 P l1 l2 ->
  forall n a b, nth_error l1 n = Some a -> nth_error l2 n = Some b -> P a b.
Proof.
  intros A B P l1. induction l1 as [| x l1 IH]; intros l2 H n a b H1 H2.
  - destruct n; simpl in H1; discriminate.
  - destruct l2 as [| y l2]; [inversion H |].
    inversion H as [| ? ? ? ? HP Hrest]; subst.
    destruct n as [| n']; simpl in *.
    + inversion H1; inversion H2; subst. exact HP.
    + apply (IH l2 Hrest n' a b); assumption.
Qed.

Lemma Permutation_concat : forall (A : Type) (l l' : list (list A)),
  Permutation l l' -> Permutation (concat l) (concat l').
Proof.
  intros A l l' H. induction H.
  - apply Permutation_refl.
  - simpl. apply Permutation_app_head. exact IHPermutation.
  - simpl. apply perm_blocks.
  - eapply Permutation_trans; [exact IHPermutation1 | exact IHPermutation2].
Qed.

Lemma J0_Permutation_l : forall s u u' v,
  Permutation u u' -> Permutation (J0 s u v) (J0 s u' v).
Proof.
  intros s u u' v H. unfold J0. apply Permutation_concat.
  apply Permutation_map. exact H.
Qed.

Lemma J0_Permutation_r : forall s u v v',
  Permutation v v' -> Permutation (J0 s u v) (J0 s u v').
Proof.
  intros s u. induction u as [| a u IH]; intros v v' H.
  - unfold J0. simpl. apply Permutation_refl.
  - unfold J0. simpl.
    fold (J0 s u v). fold (J0 s u v').
    apply Permutation_app.
    + apply Permutation_map. exact H.
    + apply IH. exact H.
Qed.

(* Multiplicities for the level-uniform typing: 3^n exceeds twice the
   sum of all lower powers, which bounds the cross-level copying demand. *)
Fixpoint sum_pow3 (n : nat) : nat :=
  match n with 0 => 0 | S n' => sum_pow3 n' + 3 ^ n' end.

Lemma sum_pow3_three : forall n, 2 * sum_pow3 n + 1 = 3 ^ n.
Proof.
  induction n as [| n IH].
  - reflexivity.
  - cbn [sum_pow3 Nat.pow]. lia.
Qed.

Lemma pow3_gt_sum : forall n, 2 * sum_pow3 n < 3 ^ n.
Proof. intro n. pose proof (sum_pow3_three n). lia. Qed.

Fixpoint sum_powB (B n : nat) : nat :=
  match n with 0 => 0 | S n' => sum_powB B n' + B ^ n' end.

Lemma sum_powB_mul : forall B n, 1 <= B ->
  (B - 1) * sum_powB B n + 1 = B ^ n.
Proof.
  intros B n HB. induction n as [| n IH].
  - cbn. lia.
  - cbn [sum_powB Nat.pow]. nia.
Qed.

Lemma powB_gt_sum : forall B n, 3 <= B -> 2 * sum_powB B n < B ^ n.
Proof.
  intros B n HB.
  assert (H1 : 1 <= B) by lia.
  pose proof (sum_powB_mul B n H1) as H.
  assert (H3 : 2 * sum_powB B n <= (B - 1) * sum_powB B n).
  { apply Nat.mul_le_mono_r. lia. }
  lia.
Qed.

Lemma J0_concat_r : forall s u v1s,
  Permutation (J0 s u (concat v1s))
              (concat (map (fun v => J0 s u v) v1s)).
Proof.
  intros s u v1s. induction v1s as [| v vs IH].
  - simpl. rewrite J0_nil_r. apply Permutation_refl.
  - simpl.
    eapply Permutation_trans.
    + apply J0_app_r.
    + apply Permutation_app.
      * apply Permutation_refl.
      * exact IH.
Qed.

Lemma J0_blocks : forall s L1s L2s,
  Permutation (J0 s (concat L1s) (concat L2s))
              (concat (flat_map (fun L1 => map (fun L2 => J0 s L1 L2) L2s) L1s)).
Proof.
  intros s L1s. induction L1s as [| L1 rest IH]; intros L2s.
  - simpl. rewrite J0_nil_l. apply Permutation_refl.
  - simpl. rewrite J0_app_l.
    eapply Permutation_trans with
      (l' := concat (map (fun L2 => J0 s L1 L2) L2s) ++
             concat (flat_map (fun L1 => map (fun L2 => J0 s L1 L2) L2s) rest)).
    + apply Permutation_app.
      * apply J0_concat_r.
      * apply IH.
    + rewrite concat_app. apply Permutation_refl.
Qed.

Lemma perm_rotate (A B C D : list nity) :
  Permutation (A ++ B ++ C ++ D) (A ++ D ++ B ++ C).
Proof.
  apply Permutation_app_head.
  rewrite app_assoc.
  apply Permutation_app_comm.
Qed.

Lemma J0_split_incl : forall s G1 G2 Gf1 Gf2 A1 A2,
  Permutation G1 (Gf1 ++ concat A1) ->
  Permutation G2 (Gf2 ++ concat A2) ->
  incl (J0 s Gf1 Gf2 ++
        concat (flat_map (fun L1 => map (fun L2 => J0 s L1 L2) A2) A1))
       (J0 s G1 G2).
Proof.
  intros s G1 G2 Gf1 Gf2 A1 A2 H1 H2.
  set (A0 := J0 s Gf1 Gf2).
  set (C1 := J0 s Gf1 (concat A2)).
  set (C2 := J0 s (concat A1) Gf2).
  set (B := J0 s (concat A1) (concat A2)).
  set (Bs := concat (flat_map (fun L1 => map (fun L2 => J0 s L1 L2) A2) A1)).
  assert (HBBs : Permutation B Bs).
  { unfold B, Bs. apply J0_blocks. }
  assert (HPerm : Permutation (J0 s G1 G2)
                              (J0 s (Gf1 ++ concat A1) (Gf2 ++ concat A2))).
  { eapply Permutation_trans.
    - apply J0_Permutation_l. exact H1.
    - apply J0_Permutation_r. exact H2. }
  assert (PermX : Permutation (J0 s (Gf1 ++ concat A1) (Gf2 ++ concat A2))
                            (A0 ++ C1 ++ C2 ++ B)).
  { unfold A0, C1, C2, B. rewrite J0_app_l.
    eapply Permutation_trans with
      (l' := (J0 s Gf1 Gf2 ++ J0 s Gf1 (concat A2)) ++
             (J0 s (concat A1) Gf2 ++ J0 s (concat A1) (concat A2))).
    - apply Permutation_app.
      + apply J0_app_r.
      + apply J0_app_r.
    - repeat rewrite app_assoc. apply Permutation_refl. }
  assert (HPermR : Permutation (J0 s (Gf1 ++ concat A1) (Gf2 ++ concat A2))
                                (A0 ++ Bs ++ C1 ++ C2)).
  { eapply Permutation_trans.
    - exact PermX.
    - eapply Permutation_trans.
      + apply perm_rotate.
      + apply Permutation_app_head. apply Permutation_app_tail. exact HBBs. }
  eapply incl_trans.
  - (* incl (A0 ++ Bs) (J0 X Y) *)
    exists [], (C1 ++ C2). simpl.
    unfold A0, Bs in HPermR. unfold A0, Bs.
    repeat rewrite app_assoc in HPermR.
    repeat rewrite app_assoc.
    exact HPermR.
  - exists [], []. simpl. rewrite app_nil_r. exact HPerm.
Qed.

Lemma parts_exists : forall n (E : environment)
    (R : nat -> list nity) (Rs : nat -> list (list nity)),
  length E = n ->
  (forall x, x < n -> incl (R x ++ concat (Rs x)) (nth x E nil)) ->
  exists Parts, length Parts = n /\
    (forall x, x < n ->
       Permutation (nth x E nil) (concat (nth x Parts nil)) /\
       Forall2 incl (R x :: Rs x) (nth x Parts nil)).
Proof.
  intros n. induction n as [| n IH]; intros E R Rs HE H.
  - destruct E as [| E0 E'].
    + exists []. split; [reflexivity | intros x Hx; lia].
    + simpl in HE; discriminate.
  - destruct E as [| E0 E'].
    + simpl in HE; discriminate.
    + simpl in HE. injection HE as HE'.
      destruct (incl_split E0 (R 0) (Rs 0) (H 0 ltac:(lia)))
        as [Ls [HP HF]].
      destruct (IH E' (fun x => R (S x)) (fun x => Rs (S x)) HE'
                (fun x Hx => H (S x) ltac:(lia)))
        as [Parts [Hlen Hprops]].
      exists (Ls :: Parts). split.
      * simpl. rewrite Hlen. reflexivity.
      * intros x Hx. destruct x as [| x'].
        -- simpl. split; [exact HP | exact HF].
        -- simpl. apply Hprops. lia.
Qed.

(* Pointwise concatenation of environments, and weakening by arbitrary
   padding.  This lets us enlarge binder entries and free-variable entries. *)

Fixpoint env_app (Gamma Delta : environment) : environment :=
  match Gamma, Delta with
  | [], Delta => Delta
  | g :: Gamma', [] => g :: env_app Gamma' []
  | g :: Gamma', d :: Delta' => (g ++ d) :: env_app Gamma' Delta'
  end.

Lemma nth_nil : forall (n : nat) (d : nity), nth n ([] : list nity) d = d.
Proof. intros n d. destruct n; reflexivity. Qed.

Lemma nth_nil_gen : forall (A : Type) (n : nat) (d : A),
  nth n ([] : list A) d = d.
Proof. intros A n d. destruct n; reflexivity. Qed.

Lemma nth_env_app :
  forall Gamma Delta x,
    nth x (env_app Gamma Delta) nil = nth x Gamma nil ++ nth x Delta nil.
Proof.
  induction Gamma as [| g G IH]; intros Delta x.
  - change (nth x Delta nil = @nth (list nity) x [] nil ++ nth x Delta nil).
    rewrite (@nth_nil_gen (list nity) x nil). rewrite app_nil_l. reflexivity.
  - destruct Delta as [| d D].
    + destruct x as [| x]; simpl.
      * rewrite app_nil_r. reflexivity.
      * specialize (IH [] x).
        rewrite (@nth_nil_gen (list nity) x nil) in IH.
        rewrite app_nil_r in IH.
        rewrite app_nil_r.
        exact IH.
    + destruct x as [| x]; simpl.
      * reflexivity.
      * apply IH.
Qed.

Lemma perm_ctx (T : Type) (A B C D : list T) :
  Permutation A (C ++ D) -> Permutation (A ++ B) ((C ++ B) ++ D).
Proof.
  intro H.
  eapply Permutation_trans.
  - apply Permutation_app; [exact H | apply Permutation_refl].
  - rewrite <- app_assoc. rewrite <- app_assoc.
    apply Permutation_app_head. apply Permutation_app_comm.
Qed.

Lemma nitlc_weaken_app Gamma M A : nitlc Gamma M A ->
  forall Delta, nitlc (env_app Gamma Delta) M A.
Proof.
  intros H.
  induction H as [G0 t x A Hssim Hin
                 | G0 Gamma' Deltas M N u A Hperm Hfunc IHfunc Hargs
                 | G0 t M u A Hssim Hbody IHbody];
    intros Delta.
  - apply nitlc_var with (t := t).
    + exact Hssim.
    + rewrite nth_env_app. apply in_app_iff. left. exact Hin.
  - apply nitlc_app with (Gamma' := env_app Gamma' Delta) (Deltas := Deltas)
      (u := u) (A := A).
    + intro x. simpl. rewrite !nth_env_app.
      simpl in Hperm.
      rewrite app_nil_r.
      eapply perm_ctx.
      eapply Permutation_trans with (l' := nth x G0 [] ++ []).
      * rewrite app_nil_r. apply Permutation_refl.
      * exact (Hperm x).
    + apply IHfunc.
    + exact Hargs.
  - apply nitlc_lam with (t := t) (u := u) (A := A).
    + exact Hssim.
    + specialize (IHbody ([] :: Delta)).
      simpl in IHbody. rewrite app_nil_r in IHbody. exact IHbody.
Qed.

Lemma nitlc_weaken_pre Gamma M A : nitlc Gamma M A ->
  forall Delta, nitlc (env_app Delta Gamma) M A.
Proof.
  intros H.
  induction H as [G0 t x A Hssim Hin
                 | G0 Gamma' Deltas M N u A Hperm Hfunc IHfunc Hargs
                 | G0 t M u A Hssim Hbody IHbody];
    intros Delta.
  - apply nitlc_var with (t := t).
    + exact Hssim.
    + rewrite nth_env_app. apply in_app_iff. right. exact Hin.
  - apply nitlc_app with (Gamma' := env_app Delta Gamma') (Deltas := Deltas)
      (u := u) (A := A).
    + intro x. simpl. rewrite !nth_env_app. rewrite app_nil_r.
      assert (Hpx : Permutation (nth x G0 nil)
                     (nth x Gamma' nil ++
                      concat (map (fun D => nth x D nil) Deltas))).
      { eapply Permutation_trans with (l' := nth x G0 nil ++ []).
        - apply Permutation_sym. apply Permutation_app_comm.
        - exact (Hperm x). }
      eapply Permutation_trans with
        (l' := nth x Delta nil ++
               (nth x Gamma' nil ++
                concat (map (fun D => nth x D nil) Deltas))).
      * apply Permutation_app_head. exact Hpx.
      * rewrite app_assoc. apply Permutation_refl.
    + apply IHfunc.
    + exact Hargs.
  - apply nitlc_lam with (t := t) (u := u) (A := A).
    + exact Hssim.
    + specialize (IHbody ([] :: Delta)).
      simpl in IHbody. exact IHbody.
Qed.

(* Padding an environment up to any length by appending empty entries.
   This is the length bookkeeping needed for uniform environments: empty
   trailing entries never carry types, so they can be added or dropped
   freely at the outer level. *)

(* Two typings of the same term at different types can be placed in one
   common environment (pointwise concatenation), because both weakenings
   preserve the type.  This is the environment-sharing half of the
   set-common synthesis. *)

Lemma nitlc_merge_same : forall M A B G1 G2,
  nitlc G1 M A -> nitlc G2 M B ->
  nitlc (env_app G1 G2) M A /\ nitlc (env_app G1 G2) M B.
Proof.
  intros M A B G1 G2 HA HB. split.
  - apply nitlc_weaken_app. exact HA.
  - apply nitlc_weaken_pre. exact HB.
Qed.

Lemma env_app_nil : forall Gamma, env_app Gamma [] = Gamma.
Proof.
  induction Gamma as [| g G IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma env_app_repeat_nil : forall Gamma k,
  env_app Gamma (repeat [] k) = Gamma ++ repeat [] (k - length Gamma).
Proof.
  induction Gamma as [| g G IH]; intros k.
  - simpl. f_equal. lia.
  - destruct k as [| k].
    + simpl. rewrite env_app_nil. rewrite app_nil_r. reflexivity.
    + simpl. rewrite app_nil_r. rewrite IH. simpl.
      replace (S k - S (length G)) with (k - length G) by lia.
      reflexivity.
Qed.

Lemma nitlc_pad_nil : forall Gamma M A, nitlc Gamma M A ->
  forall k, nitlc (Gamma ++ repeat [] (k - length Gamma)) M A.
Proof.
  intros Gamma M A H k.
  rewrite <- env_app_repeat_nil.
  apply nitlc_weaken_app. exact H.
Qed.

(* A finite family of typings of the same term at several types can be
   collected into one common environment (the pointwise concatenation of
   all their environments).  This is the environment half of the
   set-common synthesis. *)

Lemma nitlc_merge_list : forall (Us : list nity) (Gs : list environment) M,
  Forall2 (fun A G => nitlc G M A) Us Gs ->
  exists E, Forall (fun A => nitlc E M A) Us.
Proof.
  intros Us Gs M H. induction H as [| A G Us' Gs' HA Htl IH].
  - exists []. constructor.
  - destruct IH as [E HE].
    exists (env_app G E). constructor.
    + apply nitlc_weaken_app. exact HA.
    + apply Forall_forall. intros A' HA'.
      apply nitlc_weaken_pre.
      exact (proj1 (Forall_forall (fun A0 => nitlc E M A0) Us') HE A' HA').
Qed.

(* Truncating an environment whose entries are empty beyond a bound.  This
   is the dual of padding and makes environments length-uniform: all
   subderivations of an application are empty beyond the conclusion's
   length, because a permutation of the empty list is empty. *)

Definition trunc (n : nat) (G : environment) : environment := firstn n G.

Definition nil_beyond (n : nat) (G : environment) : Prop :=
  forall x, n <= x -> nth x G nil = nil.

Lemma nth_trunc_lt : forall n (G : environment) x,
  x < n -> nth x (trunc n G) nil = nth x G nil.
Proof.
  intros n G x Hx. unfold trunc. rewrite nth_firstn.
  rewrite (proj2 (Nat.ltb_lt x n) Hx). reflexivity.
Qed.

Lemma nth_trunc_ge : forall n (G : environment) x,
  n <= x -> nth x (trunc n G) nil = nil.
Proof.
  intros n G x Hx. unfold trunc. rewrite nth_firstn.
  rewrite (proj2 (Nat.ltb_ge x n) Hx). reflexivity.
Qed.

Lemma concat_eq_nil : forall (A : Type) (ls : list (list A)),
  concat ls = [] -> forall l, In l ls -> l = [].
Proof.
  intros A ls. induction ls as [| l ls IH]; intros H l' Hin.
  - destruct Hin.
  - simpl in H. apply app_eq_nil in H. destruct H as [Hl Hrest].
    destruct Hin as [Heq | Hin].
    + subst l'. exact Hl.
    + apply IH; assumption.
Qed.

Lemma nth_nil_of_concat_nil : forall (Gs : list environment) x,
  concat (map (fun D => nth x D nil) Gs) = [] ->
  forall D, In D Gs -> nth x D nil = nil.
Proof.
  intros Gs x H D HD.
  apply (concat_eq_nil nity (map (fun D => nth x D nil) Gs) H (nth x D nil)).
  apply (in_map (fun D0 => nth x D0 nil) Gs D). exact HD.
Qed.

(* The pointwise form of the environment permutation at one variable. *)
Lemma sty_perm_nth : forall (G : environment) Gs x,
  sty_permutation [G] Gs ->
  Permutation (nth x G nil) (concat (map (fun D => nth x D nil) Gs)).
Proof.
  intros G Gs x H. specialize (H x). simpl in H. rewrite app_nil_r in H. exact H.
Qed.

Lemma nth_nil_of_perm_nil : forall (G : environment) Gs x,
  sty_permutation [G] Gs -> nth x G nil = nil ->
  forall D, In D Gs -> nth x D nil = nil.
Proof.
  intros G Gs x Hperm Hx D HD.
  pose proof (sty_perm_nth G Gs x Hperm) as HP.
  rewrite Hx in HP.
  apply (nth_nil_of_concat_nil Gs x).
  - apply Permutation_nil in HP. exact HP.
  - exact HD.
Qed.

Lemma concat_map_nil_env : forall Ds : list environment,
  concat (map (fun _ : environment => (@nil nity)) Ds) = [].
Proof.
  induction Ds as [| D Ds IH]; simpl.
  - reflexivity.
  - exact IH.
Qed.

(* Removing empty trailing entries.  The induction is on the term, because
   the argument derivations inside nitlc_app's Forall2 are not recursive
   arguments of the induction principle generated for nitlc. *)
Lemma nitlc_trunc : forall M, forall n (G : environment) A,
  nil_beyond n G -> nitlc G M A -> nitlc (trunc n G) M A.
Proof.
  induction M as [x | M1 IH1 M2 IH2 | t0 M0 IH0].
  - intros n G A Hnb H.
    inversion H as [t x' A' Hssim Hin | Gp Ds N1 N2 u A' Hperm Hfun Hargs
                   | t' M' u A' Hssim Hbody]; subst.
    apply nitlc_var with (t := t).
    + exact Hssim.
    + destruct (Nat.le_gt_cases n x) as [Hge | Hlt].
      * exfalso. pose proof (Hnb x Hge) as Hnil. rewrite Hnil in Hin. destruct Hin.
      * rewrite (nth_trunc_lt n G x Hlt). exact Hin.
  - intros n G A Hnb H.
    inversion H as [t x' A' Hssim Hin | Gp Ds N1 N2 u A' Hperm Hfun Hargs
                   | t' M' u A' Hssim Hbody]; subst.
    assert (Hnb_all : forall D, In D (Gp :: Ds) -> nil_beyond n D).
    { intros D HD y Hy. apply (nth_nil_of_perm_nil G (Gp :: Ds) y Hperm).
      - apply Hnb. exact Hy.
      - exact HD. }
    assert (Hfun' : nitlc (trunc n Gp) M1 (niarr u A)).
    { apply (IH1 n Gp (niarr u A)). apply Hnb_all. left. reflexivity. exact Hfun. }
    assert (Hargs_gen : forall (u0 : list nity) (Ds0 : list environment),
      Forall2 (fun B D => nitlc D M2 B) u0 Ds0 ->
      (forall D, In D Ds0 -> nil_beyond n D) ->
      Forall2 (fun B D => nitlc D M2 B) u0
              (map (fun D => trunc n D) Ds0)).
    { intros u0. induction u0 as [| b u']; intros Ds0 Hfa HnbD.
      - inversion Hfa. simpl. constructor.
      - destruct Ds0 as [| D Ds0].
        + inversion Hfa.
        + inversion Hfa as [| b' D' u'' Ds'' Hb Htl]; subst. simpl. constructor.
          * apply (IH2 n D b). apply HnbD. left. reflexivity. exact Hb.
          * apply IHu'. exact Htl. intros E HE. apply HnbD. right. exact HE. }
    assert (Hargs' : Forall2 (fun B D => nitlc D M2 B) u
                             (map (fun D => trunc n D) Ds)).
    { apply (Hargs_gen u Ds Hargs). intros D HD. apply Hnb_all. right. exact HD. }
    apply nitlc_app with (Gamma' := trunc n Gp) (Deltas := map (fun D => trunc n D) Ds)
      (u := u) (A := A).
    + intro y. simpl. rewrite app_nil_r. rewrite map_map.
      destruct (Nat.le_gt_cases n y) as [Hge | Hlt].
      * rewrite (nth_trunc_ge n G y Hge).
        rewrite (nth_trunc_ge n Gp y Hge).
        assert (Hnils : map (fun D => nth y (trunc n D) nil) Ds
                       = map (fun _ => @nil nity) Ds).
        { apply map_ext. intro D. apply nth_trunc_ge. exact Hge. }
        rewrite Hnils. rewrite concat_map_nil_env. simpl. apply Permutation_refl.
      * rewrite (nth_trunc_lt n G y Hlt).
        rewrite (nth_trunc_lt n Gp y Hlt).
        assert (Hmap : map (fun D => nth y (trunc n D) nil) Ds
                      = map (fun D => nth y D nil) Ds).
        { apply map_ext. intro D. apply nth_trunc_lt. exact Hlt. }
        rewrite Hmap.
        pose proof (Hperm y) as HP. simpl in HP. rewrite app_nil_r in HP. exact HP.
    + exact Hfun'.
    + exact Hargs'.
  - intros n G A Hnb H.
    inversion H as [t x' A' Hssim Hin | Gp Ds N1 N2 u A' Hperm Hfun Hargs
                   | t' M' u A' Hssim Hbody]; subst.
    apply nitlc_lam with (t := t0) (u := u) (A := A').
    + exact Hssim.
    + assert (Hnb' : nil_beyond (S n) (cons u G)).
      { intros y Hy. destruct y as [| y'].
        - simpl. exfalso; lia.
        - simpl. apply Hnb. lia. }
      specialize (IH0 (S n) (cons u G) A' Hnb' Hbody).
      replace (trunc (S n) (cons u G)) with (cons u (trunc n G)) in IH0.
      * exact IH0.
      * unfold trunc. rewrite firstn_cons. reflexivity.
Qed.

(* Normalizing an environment to an exact outer length: truncate at n and
   pad with empty entries.  Entries below n are preserved, so this is the
   canonical length-uniform representative of an environment that is empty
   beyond n. *)

Definition norm (n : nat) (G : environment) : environment :=
  trunc n G ++ repeat [] (n - length (trunc n G)).

Lemma length_norm : forall n (G : environment), length (norm n G) = n.
Proof.
  intros n G. unfold norm. rewrite length_app, repeat_length.
  pose proof (firstn_le_length n G) as Hle. unfold trunc in Hle.
  rewrite Nat.add_comm. rewrite Nat.sub_add; [reflexivity | exact Hle].
Qed.

Lemma nth_ge_length : forall (l : environment) x,
  length l <= x -> nth x l nil = nil.
Proof.
  induction l as [| a l IH]; intros x H; simpl in *.
  - destruct x; reflexivity.
  - destruct x as [| x].
    + lia.
    + simpl. apply IH. lia.
Qed.

Lemma nth_norm_lt : forall n (G : environment) x,
  x < n -> nth x (norm n G) nil = nth x G nil.
Proof.
  intros n G x Hx. unfold norm.
  destruct (Nat.lt_ge_cases x (length (trunc n G))) as [Hlt | Hge].
  - rewrite app_nth1; [| exact Hlt].
    rewrite nth_trunc_lt; [reflexivity | exact Hx].
  - rewrite (app_nth2 (trunc n G) (repeat [] (n - length (trunc n G))) nil Hge).
    rewrite nth_repeat.
    symmetry. apply nth_overflow.
    assert (Hmin : length (trunc n G) = Nat.min n (length G)).
    { unfold trunc. apply length_firstn. }
    destruct (Nat.lt_ge_cases (length G) n) as [Hlen | Hlen].
    + rewrite Nat.min_r in Hmin by lia. lia.
    + rewrite Nat.min_l in Hmin by lia. exfalso; lia.
Qed.

Lemma nth_norm_ge : forall n (G : environment) x,
  n <= x -> nth x (norm n G) nil = nil.
Proof.
  intros n G x Hx. apply nth_overflow. rewrite length_norm. exact Hx.
Qed.

Lemma nitlc_norm : forall n (G : environment) M A,
  nil_beyond n G -> nitlc G M A -> nitlc (norm n G) M A.
Proof.
  intros n G M A Hnb H. unfold norm.
  apply nitlc_pad_nil.
  apply nitlc_trunc with (n := n); assumption.
Qed.

(* Canonical ("thin") type of a simple type, and the fact that it is the
   bottom of the support-preserving inflation order. *)

Fixpoint ct (s : sty) : nity :=
  match s with
  | satom a => niatom a
  | sarr s1 s2 => niarr [ct s1] (ct s2)
  end.

Lemma ssim_ct s : ssim s (ct s).
Proof.
  induction s as [a | s1 IHs1 s2 IHs2]; simpl.
  - constructor.
  - apply ssim_arr.
    + constructor.
      * exact IHs1.
      * constructor.
    + exact IHs2.
Qed.

Lemma ct_bottom s A : ssim s A -> nle2 (ct s) A.
Proof.
  revert A. induction s as [a | s1 IHs1 s2 IHs2]; intros A HA.
  - inversion HA. simpl. constructor.
  - inversion HA as [x | sA1 sA2 A0 u0 Bss Hfa Hssim]; subst. simpl.
    constructor.
    + intros b Hb. exists (ct s1). split; [left; reflexivity |].
      apply IHs1. exact (proj1 (Forall_forall (ssim s1) (A0 :: u0)) Hfa b Hb).
    + intros a Ha. simpl in Ha. destruct Ha as [Heq | Hnil].
      * subst a. exists A0. split; [left; reflexivity |].
        apply IHs1. exact (Forall_inv Hfa).
      * destruct Hnil.
    + apply IHs2. exact Hssim.
Qed.

(* A constant lambda: the binder is unused, so its entry is arbitrary
   non-empty padding while the free variable at position 1 carries B. *)
Lemma nitlc_lam_const u B s t :
  u <> [] -> Forall (ssim s) u -> ssim t B ->
  nitlc [[B]] (lam (sarr s t) (var 1)) (niarr u B).
Proof.
  intros Hne Hfa Hssim.
  destruct u as [| a u'].
  - exfalso. exact (Hne eq_refl).
  - apply nitlc_lam with (t := sarr s t) (u := a :: u') (A := B).
    + apply ssim_arr.
      * exact Hfa.
      * exact Hssim.
    + simpl. apply nitlc_var with (t := t).
      * exact Hssim.
      * simpl. left. reflexivity.
Qed.

(* Padding an environment with the canonical type of each simple variable
   makes every entry non-empty while preserving the collapse condition. *)

Fixpoint pads (Gamma0 : list sty) : environment :=
  match Gamma0 with
  | [] => []
  | s :: Gamma0' => [ct s] :: pads Gamma0'
  end.

Lemma finish_env : forall Gamma0 Gamma M A,
  nitlc Gamma M A ->
  Forall2 (fun s u => Forall (ssim s) u) Gamma0 Gamma ->
  exists Gamma', nitlc Gamma' M A /\
    Forall2 (fun s u => u <> [] /\ Forall (ssim s) u) Gamma0 Gamma'.
Proof.
  intros Gamma0 Gamma M A Hder Hfa2.
  exists (env_app Gamma (pads Gamma0)). split.
  - apply nitlc_weaken_app. exact Hder.
  - clear Hder. revert Gamma Hfa2.
    induction Gamma0 as [| s Gamma0 IH]; intros Gamma Hfa2.
    + inversion Hfa2. constructor.
    + inversion Hfa2 as [| x y l l' Hhead Htail]; subst.
      constructor.
      * split.
        -- intro E. destruct (app_eq_nil _ _ E) as [_ E2]. discriminate E2.
        -- apply Forall_app. split.
           ++ exact Hhead.
           ++ constructor; [apply ssim_ct | constructor].
      * apply IH. exact Htail.
Qed.

(* The identity lambda at any argument list containing its result type. *)
Lemma nitlc_lam_id_gen u A s :
  u <> [] -> In A u -> Forall (ssim s) u -> ssim s A ->
  nitlc [] (lam (sarr s s) (var 0)) (niarr u A).
Proof.
  intros Hne Hin Hfa Hssim.
  destruct u as [| a u'].
  - exfalso. exact (Hne eq_refl).
  - apply nitlc_lam with (t := sarr s s) (u := a :: u') (A := A).
    + apply ssim_arr; assumption.
    + simpl. apply nitlc_var with (t := s).
      * exact Hssim.
      * exact Hin.
Qed.

(* A non-empty list of types of the same simple type has a common nle2
   upper bound.  This is the join tool used by the contextual synthesis. *)
Lemma nle2_ssim_of_upper :
  forall l C s, l <> [] -> Forall (ssim s) l ->
    Forall (fun A => nle2 A C) l -> ssim s C.
Proof.
  intros l C s Hne Hfa Hle.
  destruct l as [| a l'].
  - exfalso; exact (Hne eq_refl).
  - apply nle2_ssim with (A := a).
    + exact (Forall_inv Hle).
    + exact (Forall_inv Hfa).
Qed.

Lemma nle2_upper_list :
  forall l s, l <> [] -> Forall (ssim s) l ->
    exists C, Forall (fun A => nle2 A C) l.
Proof.
  intros l. induction l as [| a l' IH]; intros s Hne Hfa.
  - exfalso; exact (Hne eq_refl).
  - destruct l' as [| b l''].
    + exists a. constructor; [apply nle2_refl | constructor].
    + assert (Hne' : b :: l'' <> []) by discriminate.
      assert (Hfa' : Forall (ssim s) (b :: l''))
        by (apply (Forall_inv_tail Hfa)).
      destruct (IH s Hne' Hfa') as [C' HC'].
      assert (HssimC' : ssim s C').
      { apply (nle2_ssim_of_upper (b :: l'') C' s); assumption. }
      destruct (nle2_directed s a C'
                  (Forall_inv Hfa) HssimC') as [C [Ha HC]].
      exists C. constructor.
      * exact Ha.
      * apply (proj2 (Forall_forall (fun A => nle2 A C) (b :: l''))).
        intros x Hx.
        apply (nle2_trans x C' C).
        -- exact (proj1 (Forall_forall (fun A => nle2 A C') (b :: l''))
                    HC' x Hx).
        -- exact HC.
Qed.

(* The sequential inflation nle is a subrelation of the cover inflation
   nle2, and nle_list yields the two cover conditions. *)
Lemma nle2_of_nle_all :
  forall x : nity + list nity,
    match x with
    | inl A => forall B, nle A B -> nle2 A B
    | inr u => forall v, nle_list u v ->
        (forall b, In b v -> exists a, In a u /\ nle2 a b) /\
        (forall a, In a u -> exists b, In b v /\ nle2 a b)
    end.
Proof.
  refine (well_founded_ind
            (@wf_inverse_image (nity + list nity) nat lt msize lt_wf)
            (fun x => match x with
                      | inl A => forall B, nle A B -> nle2 A B
                      | inr u => forall v, nle_list u v ->
                          (forall b, In b v -> exists a, In a u /\ nle2 a b) /\
                          (forall a, In a u -> exists b, In b v /\ nle2 a b)
                      end) _).
  intros [A | u] IH.
  - intros B Hnle. destruct Hnle as [x | u' A' v' B' Hlist Hle].
    + constructor.
    + assert (Hm : msize (inr u') < msize (inl (niarr u' A'))).
      { change (lsize u' < nsize (niarr u' A')). rewrite nsize_niarr.
        pose proof (nsize_pos A'). lia. }
      pose proof (IH (inr u') Hm v' Hlist) as [Hc1 Hc2].
      assert (HmA : msize (inl A') < msize (inl (niarr u' A'))).
      { change (nsize A' < nsize (niarr u' A')). rewrite nsize_niarr.
        pose proof (nsize_pos A'). lia. }
      apply nle2_arr.
      * exact Hc1.
      * exact Hc2.
      * exact (IH (inl A') HmA B' Hle).
  - intros v Hlist. destruct Hlist as [| a u' vblock vtail Hne Hfa Htail].
    + split.
      * intros b Hb. destruct Hb.
      * intros a0 Ha0. destruct Ha0.
    + assert (Hma : msize (inl a) < msize (inr (a :: u'))).
      { change (nsize a < lsize (a :: u')). rewrite lsize_cons. lia. }
      assert (Hmu : msize (inr u') < msize (inr (a :: u'))).
      { change (lsize u' < lsize (a :: u')). rewrite lsize_cons. lia. }
      split.
      * intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb | Hb].
        -- pose proof (proj1 (Forall_forall (nle a) vblock) Hfa b Hb) as Hab.
           exists a. split; [left; reflexivity |].
           exact (IH (inl a) Hma b Hab).
        -- destruct (IH (inr u') Hmu vtail Htail) as [Hc1 Hc2].
           destruct (Hc1 b Hb) as [a' [Ha' Hab]].
           exists a'. split; [right; exact Ha' | exact Hab].
      * intros a0 Ha0. destruct Ha0 as [Heq | Ha0].
        -- subst a0. destruct vblock as [| b vblock'].
           ++ exfalso; exact (Hne eq_refl).
           ++ exists b. split; [apply in_or_app; left; left; reflexivity |].
              apply (IH (inl a) Hma). exact (Forall_inv Hfa).
        -- destruct (IH (inr u') Hmu vtail Htail) as [Hc1 Hc2].
           destruct (Hc2 a0 Ha0) as [b [Hb Hab]].
           exists b. split; [apply in_or_app; right; exact Hb | exact Hab].
Qed.

Lemma nle2_cover_list u v : nle_list u v ->
  (forall b, In b v -> exists a, In a u /\ nle2 a b) /\
  (forall a, In a u -> exists b, In b v /\ nle2 a b).
Proof. intros H. exact (nle2_of_nle_all (inr u) v H). Qed.

(* Mutual self-support-preserving inflation. *)
Inductive sle : nity -> nity -> Prop :=
| sle_atom x : sle (niatom x) (niatom x)
| sle_arr u A v B :
    sle_list u v -> sle A B -> (In A u -> In B v) ->
    sle (niarr u A) (niarr v B)
with sle_list : list nity -> list nity -> Prop :=
| sle_list_nil : sle_list [] []
| sle_list_cons a u v v' :
    v <> [] -> Forall (sle a) v -> sle_list u v' ->
    sle_list (a :: u) (v ++ v').

Lemma sle_refl_all :
  forall x : nity + list nity,
    match x with
    | inl A => sle A A
    | inr u => sle_list u u
    end.
Proof.
  refine (well_founded_ind
            (@wf_inverse_image (nity + list nity) nat lt msize lt_wf)
            (fun x => match x with inl A => sle A A | inr u => sle_list u u end) _).
  intros [A | u] IH.
  - destruct A as [x | u A].
    + constructor.
    + constructor.
      * apply (IH (inr u)).
        change (lsize u < nsize (niarr u A)). rewrite nsize_niarr.
        pose proof (nsize_pos A). lia.
      * apply (IH (inl A)).
        change (nsize A < nsize (niarr u A)). rewrite nsize_niarr.
        pose proof (nsize_pos A). lia.
      * intros H. exact H.
  - destruct u as [| a u'].
    + constructor.
    + apply (sle_list_cons a u' [a] u').
      * discriminate.
      * constructor.
        -- apply (IH (inl a)).
           change (nsize a < lsize (a :: u')). rewrite lsize_cons. lia.
        -- constructor.
      * apply (IH (inr u')).
        change (lsize u' < lsize (a :: u')). rewrite lsize_cons. lia.
Qed.

Lemma sle_refl A : sle A A.
Proof. exact (sle_refl_all (inl A)). Qed.

Lemma sle_list_refl u : sle_list u u.
Proof. exact (sle_refl_all (inr u)). Qed.

Lemma sle_list_nonempty u v : sle_list u v -> u <> [] -> v <> [].
Proof.
  intros H. induction H as [| a u vblock vtail Hne Hfa Htail IH]; intro Hu.
  - exact Hu.
  - intro Hv. apply app_eq_nil in Hv. destruct Hv as [E _]. exact (Hne E).
Qed.

Lemma sle_ssim_all :
  forall x : nity + list nity,
    match x with
    | inl A => forall B s, sle A B -> ssim s A -> ssim s B
    | inr u => forall v s, sle_list u v ->
               Forall (ssim s) u -> Forall (ssim s) v
    end.
Proof.
  refine (well_founded_ind
            (@wf_inverse_image (nity + list nity) nat lt msize lt_wf)
            (fun x => match x with
                      | inl A => forall B s, sle A B -> ssim s A -> ssim s B
                      | inr u => forall v s, sle_list u v ->
                                 Forall (ssim s) u -> Forall (ssim s) v
                      end) _).
  intros [A | u] IH.
  - intros B s Hnle Hssim.
    destruct Hnle as [x | u' A' v' B' Hlist Hle Hcond].
    + inversion Hssim. constructor.
    + inversion Hssim as [x | s1 s2 A0 u0 Bss Hfa Hssim2]; subst.
      destruct v' as [| b v''].
      * exfalso.
        assert (Hne0 : A0 :: u0 <> []) by (intro E; discriminate E).
        exact (sle_list_nonempty (A0 :: u0) [] Hlist Hne0 eq_refl).
      * apply ssim_arr.
        -- assert (Hm : msize (inr (A0 :: u0)) < msize (inl (niarr (A0 :: u0) A'))).
           { change (lsize (A0 :: u0) < nsize (niarr (A0 :: u0) A')).
             rewrite nsize_niarr. pose proof (nsize_pos A'). lia. }
           exact (IH (inr (A0 :: u0)) Hm (b :: v'') s1 Hlist Hfa).
        -- assert (Hm : msize (inl A') < msize (inl (niarr (A0 :: u0) A'))).
           { change (nsize A' < nsize (niarr (A0 :: u0) A')).
             rewrite nsize_niarr. pose proof (nsize_pos A'). lia. }
           exact (IH (inl A') Hm B' s2 Hle Hssim2).
  - intros v s Hlist Hfa.
    destruct Hlist as [| a u' vblock vtail Hne Hfa_block Htail].
    + constructor.
    + apply Forall_app. split.
      * apply (proj2 (Forall_forall (ssim s) vblock)). intros b Hb.
        assert (Hm : msize (inl a) < msize (inr (a :: u'))).
        { change (nsize a < lsize (a :: u')). rewrite lsize_cons. lia. }
        exact (IH (inl a) Hm b s
                 (proj1 (Forall_forall (sle a) vblock) Hfa_block b Hb)
                 (Forall_inv Hfa)).
      * assert (Hm : msize (inr u') < msize (inr (a :: u'))).
        { change (lsize u' < lsize (a :: u')). rewrite lsize_cons. lia. }
        exact (IH (inr u') Hm vtail s Htail (Forall_inv_tail Hfa)).
Qed.

Lemma sle_ssim A B s : sle A B -> ssim s A -> ssim s B.
Proof. intros H1 H2. exact (sle_ssim_all (inl A) B s H1 H2). Qed.

Lemma sle_list_ssim u v s :
  sle_list u v -> Forall (ssim s) u -> Forall (ssim s) v.
Proof. intros H1 H2. exact (sle_ssim_all (inr u) v s H1 H2). Qed.

Lemma sle_nle2_all :
  forall x : nity + list nity,
    match x with
    | inl A => forall B, sle A B -> nle2 A B
    | inr u => forall v, sle_list u v ->
        (forall b, In b v -> exists a, In a u /\ nle2 a b) /\
        (forall a, In a u -> exists b, In b v /\ nle2 a b)
    end.
Proof.
  refine (well_founded_ind
            (@wf_inverse_image (nity + list nity) nat lt msize lt_wf)
            (fun x => match x with
                      | inl A => forall B, sle A B -> nle2 A B
                      | inr u => forall v, sle_list u v ->
                          (forall b, In b v -> exists a, In a u /\ nle2 a b) /\
                          (forall a, In a u -> exists b, In b v /\ nle2 a b)
                      end) _).
  intros [A | u] IH.
  - intros B Hsle. destruct Hsle as [x | u' A' v' B' Hlist Hle Hcond].
    + constructor.
    + assert (Hm : msize (inr u') < msize (inl (niarr u' A'))).
      { change (lsize u' < nsize (niarr u' A')). rewrite nsize_niarr.
        pose proof (nsize_pos A'). lia. }
      pose proof (IH (inr u') Hm v' Hlist) as [Hc1 Hc2].
      assert (HmA : msize (inl A') < msize (inl (niarr u' A'))).
      { change (nsize A' < nsize (niarr u' A')). rewrite nsize_niarr.
        pose proof (nsize_pos A'). lia. }
      apply nle2_arr.
      * exact Hc1.
      * exact Hc2.
      * exact (IH (inl A') HmA B' Hle).
  - intros v Hlist. destruct Hlist as [| a u' vblock vtail Hne Hfa Htail].
    + split.
      * intros b Hb. destruct Hb.
      * intros a0 Ha0. destruct Ha0.
    + assert (Hma : msize (inl a) < msize (inr (a :: u'))).
      { change (nsize a < lsize (a :: u')). rewrite lsize_cons. lia. }
      assert (Hmu : msize (inr u') < msize (inr (a :: u'))).
      { change (lsize u' < lsize (a :: u')). rewrite lsize_cons. lia. }
      split.
      * intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb | Hb].
        -- pose proof (proj1 (Forall_forall (sle a) vblock) Hfa b Hb) as Hab.
           exists a. split; [left; reflexivity |].
           exact (IH (inl a) Hma b Hab).
        -- destruct (IH (inr u') Hmu vtail Htail) as [Hc1 Hc2].
           destruct (Hc1 b Hb) as [a' [Ha' Hab]].
           exists a'. split; [right; exact Ha' | exact Hab].
      * intros a0 Ha0. destruct Ha0 as [Heq | Ha0].
        -- subst a0. destruct vblock as [| b vblock'].
           ++ exfalso; exact (Hne eq_refl).
           ++ exists b. split; [apply in_or_app; left; left; reflexivity |].
              apply (IH (inl a) Hma). exact (Forall_inv Hfa).
        -- destruct (IH (inr u') Hmu vtail Htail) as [Hc1 Hc2].
           destruct (Hc2 a0 Ha0) as [b [Hb Hab]].
           exists b. split; [apply in_or_app; right; exact Hb | exact Hab].
Qed.

Lemma sle_nle2 A B : sle A B -> nle2 A B.
Proof. intros H. exact (sle_nle2_all (inl A) B H). Qed.

Lemma sle_list_cover u v : sle_list u v ->
  (forall b, In b v -> exists a, In a u /\ nle2 a b) /\
  (forall a, In a u -> exists b, In b v /\ nle2 a b).
Proof. intros H. exact (sle_nle2_all (inr u) v H). Qed.

Lemma sle_list_cover_sle u v : sle_list u v ->
  (forall a, In a u -> exists b, In b v /\ sle a b).
Proof.
  induction 1 as [| a u vblock vtail Hne Hfa Htail IH].
  - intros a Ha. destruct Ha.
  - intros a0 Ha0. destruct Ha0 as [Heq | Ha0].
    + subst a0. destruct vblock as [| b vblock'].
      * exfalso. exact (Hne eq_refl).
      * exists b. split.
        -- apply in_or_app. left. left. reflexivity.
        -- exact (Forall_inv Hfa).
    + destruct (IH a0 Ha0) as [b [Hb Hab]].
      exists b. split.
      * apply in_or_app. right. exact Hb.
      * exact Hab.
Qed.

Lemma sle_list_app_split :
  forall u1 u2 v, sle_list (u1 ++ u2) v ->
  exists v1 v2, v = v1 ++ v2 /\ sle_list u1 v1 /\ sle_list u2 v2.
Proof.
  induction u1 as [| a u1 IH]; intros u2 v H.
  - simpl in H. exists [], v. split.
    + rewrite app_nil_l. reflexivity.
    + split; [constructor | exact H].
  - simpl in H.
    inversion H as [| a0 u0 vblock vtail Hne Hfa Htail]; subst.
    destruct (IH u2 vtail Htail) as [v1' [v2 [Heq [Hl1 Hl2]]]].
    exists (vblock ++ v1'), v2. split.
    + rewrite Heq. rewrite app_assoc. reflexivity.
    + split.
      * apply (sle_list_cons a u1 vblock v1' Hne Hfa Hl1).
      * exact Hl2.
Qed.

(* Decidable equality on simple types, and the compatibility predicate on
   nity targets: at every arrow whose source and target simple types
   coincide, the result must occur in the argument list.  This is the
   condition that makes var-at-root retargeting sound. *)
Fixpoint sty_eqb (s t : sty) : bool :=
  match s, t with
  | satom a, satom b => Nat.eqb a b
  | sarr s1 s2, sarr t1 t2 => andb (sty_eqb s1 t1) (sty_eqb s2 t2)
  | _, _ => false
  end.

Lemma sty_eqb_eq : forall s t, sty_eqb s t = true <-> s = t.
Proof.
  induction s; destruct t; simpl; try (split; discriminate).
  - rewrite Nat.eqb_eq. split; intro H.
    + subst. reflexivity.
    + inversion H. reflexivity.
  - rewrite andb_true_iff, IHs1, IHs2. split; intro H.
    + destruct H as [H1 H2]. subst. reflexivity.
    + inversion H. split; reflexivity.
Qed.

Fixpoint compat (s : sty) (A : nity) : Prop :=
  match s, A with
  | satom a, niatom x => a = x
  | sarr s1 s2, niarr u B =>
      u <> [] /\ Forall (compat s1) u /\ compat s2 B /\
      (if sty_eqb s1 s2 then In B u else True)
  | _, _ => False
  end.

Lemma compat_ct : forall s, compat s (ct s).
Proof.
  induction s as [a | s1 IHs1 s2 IHs2]; simpl.
  - reflexivity.
  - split; [discriminate |]. split.
    + constructor; [exact IHs1 | constructor].
    + split; [exact IHs2 |].
      destruct (sty_eqb s1 s2) eqn:E.
      * apply sty_eqb_eq in E. subst s2. left. reflexivity.
      * exact I.
Qed.

Lemma compat_ssim_all :
  forall x : nity + list nity,
    match x with
    | inl A => forall s, compat s A -> ssim s A
    | inr u => forall s, Forall (compat s) u -> Forall (ssim s) u
    end.
Proof.
  refine (well_founded_ind
            (@wf_inverse_image (nity + list nity) nat lt msize lt_wf)
            (fun x => match x with
                      | inl A => forall s, compat s A -> ssim s A
                      | inr u => forall s, Forall (compat s) u -> Forall (ssim s) u
                      end) _).
  intros [A | u] IH.
  - intros s H. destruct A as [x | v B]; destruct s as [a | s1 s2]; simpl in H.
    + subst x. constructor.
    + contradiction.
    + contradiction.
    + destruct H as [Hne [Hfa [HB Hcond]]].
      destruct v as [| c v'].
      * contradiction.
      * apply ssim_arr.
        -- assert (Hm : msize (inr (c :: v')) < msize (inl (niarr (c :: v') B))).
           { change (lsize (c :: v') < nsize (niarr (c :: v') B)).
             rewrite nsize_niarr. pose proof (nsize_pos B). lia. }
           exact (IH (inr (c :: v')) Hm s1 Hfa).
        -- assert (Hm : msize (inl B) < msize (inl (niarr (c :: v') B))).
           { change (nsize B < nsize (niarr (c :: v') B)).
             rewrite nsize_niarr. pose proof (nsize_pos B). lia. }
           exact (IH (inl B) Hm s2 HB).
  - intros s Hfa. destruct u as [| a u'].
    + constructor.
    + constructor.
      * assert (Hm : msize (inl a) < msize (inr (a :: u'))).
        { change (nsize a < lsize (a :: u')). rewrite lsize_cons. lia. }
        exact (IH (inl a) Hm s (Forall_inv Hfa)).
      * assert (Hm : msize (inr u') < msize (inr (a :: u'))).
        { change (lsize u' < lsize (a :: u')). rewrite lsize_cons. lia. }
        exact (IH (inr u') Hm s (Forall_inv_tail Hfa)).
Qed.

Lemma compat_ssim s A : compat s A -> ssim s A.
Proof. intros H. exact (compat_ssim_all (inl A) s H). Qed.

Lemma compat_forall_ssim s u : Forall (compat s) u -> Forall (ssim s) u.
Proof. intros H. exact (compat_ssim_all (inr u) s H). Qed.

Lemma sty_eqb_refl : forall s, sty_eqb s s = true.
Proof. intro s. apply sty_eqb_eq. reflexivity. Qed.

(* Every ssim type has a compat nle2-upper bound. *)
Lemma comp_exists : forall s A, ssim s A -> exists C, nle2 A C /\ compat s C.
Proof.
  induction s as [a | s1 IHs1 s2 IHs2]; intros A HA.
  - inversion HA; subst. exists (niatom a). split; [apply nle2_refl | simpl; reflexivity].
  - inversion HA as [x | sA sB A0 u B0 HAfa Hssim]; subst.
    assert (Hrows : forall a0, In a0 (A0 :: u) ->
              exists C, nle2 a0 C /\ compat s1 C).
    { intros a0 Ha0. apply IHs1.
      exact (proj1 (Forall_forall (ssim s1) (A0 :: u)) HAfa a0 Ha0). }
    destruct (Forall2_exists_gen nity nity (A0 :: u)
                (fun a0 C => nle2 a0 C /\ compat s1 C) Hrows) as [w Hw].
    destruct (IHs2 B0 Hssim) as [C2 [HB0C2 HcC2]].
    destruct (sty_eqb s1 s2) eqn:E.
    + apply sty_eqb_eq in E. subst s2.
      destruct (nle2_directed s1 B0 A0 Hssim
                  (proj1 (Forall_forall (ssim s1) (A0 :: u)) HAfa A0 (or_introl eq_refl)))
        as [D [HB0D HA0D]].
      destruct (IHs2 D (nle2_ssim B0 D s1 HB0D Hssim)) as [Bj [HDB HcB]].
      exists (niarr (Bj :: w) Bj). split.
      * apply nle2_arr.
        -- intros c Hc. destruct Hc as [Heq | Hc].
           ++ subst c. exists A0. split; [left; reflexivity |].
              exact (nle2_trans A0 D Bj HA0D HDB).
           ++ destruct (Forall2_in_right (fun a0 C => nle2 a0 C /\ compat s1 C) (A0::u) w c Hw Hc)
                as [a0 [Ha0 Hnle]].
              exists a0. split; [exact Ha0 | exact (proj1 Hnle)].
        -- intros a0 Ha0. destruct Ha0 as [Heq | Ha0].
           ++ subst a0. exists Bj. split; [left; reflexivity |].
              exact (nle2_trans A0 D Bj HA0D HDB).
           ++ destruct (Forall2_in_left (fun a0 C => nle2 a0 C /\ compat s1 C) (A0::u) w a0 Hw (or_intror Ha0))
                as [C [HC Hnle]].
              exists C. split; [right; exact HC | exact (proj1 Hnle)].
        -- exact (nle2_trans B0 D Bj HB0D HDB).
      * simpl. split; [intro E0; discriminate E0 |]. split.
        -- apply Forall_cons; [exact HcB |].
           apply (proj2 (Forall_forall (compat s1) w)).
           intros C HC. destruct (Forall2_in_right (fun a0 C => nle2 a0 C /\ compat s1 C) (A0::u) w C Hw HC)
             as [a0 [Ha0 Hnle]]. exact (proj2 Hnle).
        -- split; [exact HcB |].
           rewrite sty_eqb_refl. left; reflexivity.
    + exists (niarr w C2). split.
      * apply nle2_arr.
        -- intros c Hc. destruct (Forall2_in_right (fun a0 C => nle2 a0 C /\ compat s1 C) (A0::u) w c Hw Hc)
                as [a0 [Ha0 Hnle]]. exists a0. split; [exact Ha0 | exact (proj1 Hnle)].
        -- intros a0 Ha0. destruct (Forall2_in_left (fun a0 C => nle2 a0 C /\ compat s1 C) (A0::u) w a0 Hw Ha0)
                as [C [HC Hnle]]. exists C. split; [exact HC | exact (proj1 Hnle)].
        -- exact HB0C2.
      * simpl. split.
        -- destruct (Forall2_in_left (fun a0 C => nle2 a0 C /\ compat s1 C) (A0::u) w A0 Hw (or_introl eq_refl))
             as [C [HC _]].
           intro Ew; rewrite Ew in HC; destruct HC.
        -- split.
           ++ apply (proj2 (Forall_forall (compat s1) w)). intros C HC.
              destruct (Forall2_in_right (fun a0 C => nle2 a0 C /\ compat s1 C) (A0::u) w C Hw HC)
                as [a0 [Ha0 Hnle]]. exact (proj2 Hnle).
           ++ split; [exact HcC2 | rewrite E; exact I].
Qed.

(* Compatible directedness follows by completing a common nle2 upper bound. *)
Lemma compat_join : forall s A B,
  ssim s A -> ssim s B -> exists C, nle2 A C /\ nle2 B C /\ compat s C.
Proof.
  intros s A B HA HB.
  destruct (nle2_directed s A B HA HB) as [C0 [HAC0 HBC0]].
  destruct (comp_exists s C0 (nle2_ssim A C0 s HAC0 HA)) as [C [HC0C Hc]].
  exists C. split; [apply (nle2_trans A C0 C HAC0 HC0C) |].
  split; [apply (nle2_trans B C0 C HBC0 HC0C) | exact Hc].
Qed.


Fixpoint V (B D L : nat) (s : sty) : nity :=
  match s with
  | satom a => niatom a
  | sarr s1 s2 =>
      niarr (concat (map (fun Q => repeat (V B D Q s1) (S (B ^ (Q - L))))
                           (seq 0 (S D))))
            (V B D L s2)
  end.

Lemma V_args_nonempty : forall B D L s1,
  concat (map (fun Q => repeat (V B D Q s1) (S (B ^ (Q - L))))
              (seq 0 (S D))) <> [].
Proof.
  intros B D L s1 E.
  assert (Hin : In (V B D 0 s1)
    (concat (map (fun Q => repeat (V B D Q s1) (S (B ^ (Q - L))))
                 (seq 0 (S D))))).
  { apply in_concat. exists (repeat (V B D 0 s1) (S (B ^ (0 - L)))).
    split.
    - apply in_map_iff. exists 0. split; [reflexivity |].
      apply in_seq. lia.
    - simpl. left. reflexivity. }
  rewrite E in Hin. destruct Hin.
Qed.

Lemma ssim_V : forall B D L s, ssim s (V B D L s).
Proof.
  intros B D L s. revert B D L. induction s as [a | s1 IHs1 s2 IHs2]; intros B D L; simpl.
  - constructor.
  - assert (Hne : concat (map (fun Q => repeat (V B D Q s1) (S (B ^ (Q - L))))
                                (seq 0 (S D))) <> []).
    { apply V_args_nonempty. }
    remember (concat (map (fun Q => repeat (V B D Q s1) (S (B ^ (Q - L))))
                              (seq 0 (S D)))) as Lst eqn:EL.
    assert (Hfa : Forall (ssim s1) Lst).
    { rewrite EL. apply Forall_forall. intros e He.
      rewrite in_concat in He. destruct He as [l [Hin Hel]].
      rewrite in_map_iff in Hin. destruct Hin as [Q [HQ Hl]]; subst l.
      pose proof (repeat_spec (S (B ^ (Q - L))) (V B D Q s1) e Hel) as Heq.
      subst e. apply IHs1. }
    destruct Lst as [| h t].
    { exfalso. exact (Hne eq_refl). }
    apply ssim_arr.
    + rewrite EL in Hfa. exact Hfa.
    + apply IHs2.
Qed.


(* ===== Environment monotonicity infrastructure ===== *)

Definition eincl (G E : environment) : Prop :=
  forall x, incl (nth x G nil) (nth x E nil).

Lemma incl_perm (l l' : list nity) : Permutation l l' -> incl l l'.
Proof.
  intro H. exists [], []. simpl. rewrite app_nil_r. apply Permutation_sym. exact H.
Qed.

Lemma incl_perm_r (l l' L : list nity) :
  Permutation l l' -> incl l' L -> incl l L.
Proof. intros HP Hi. apply (incl_trans l l' L). apply incl_perm. exact HP. exact Hi. Qed.

Lemma incl_of_perm : forall l l' L, Permutation l l' -> incl l L -> incl l' L.
Proof.
  intros l l' L HP Hi. apply (incl_trans l' l L).
  - apply incl_perm. apply Permutation_sym. exact HP.
  - exact Hi.
Qed.

Lemma Forall2_nth0 : forall (P : nity -> environment -> Prop) a b l l',
  Forall2 P (a :: l) (b :: l') -> P a b.
Proof. intros. inversion H. assumption. Qed.

Lemma Forall2_incl_nth_i : forall (A B : list (list nity)) i,
  Forall2 incl A B -> i < length A -> incl (nth i A nil) (nth i B nil).
Proof.
  intros A B i H. revert i.
  induction H as [| a b A' B' Hab Hrest IH]; intros i Hi.
  - simpl in Hi; lia.
  - destruct i as [| i']; simpl.
    + exact Hab.
    + apply IH. simpl in Hi; lia.
Qed.

Lemma nth_map_lt : forall (A B : Type) (f : A -> B) (l : list A) i (d : B) (da : A),
  i < length l -> nth i (map f l) d = f (nth i l da).
Proof.
  intros A B f l. induction l as [| a l IH]; intros i d da Hi.
  - simpl in Hi; lia.
  - destruct i as [| i']; simpl.
    + reflexivity.
    + apply IH. simpl in Hi; lia.
Qed.

Lemma nth_seq_0 : forall i k, i < k -> nth i (seq 0 k) 0 = i.
Proof.
  intros i k Hi. rewrite seq_nth by exact Hi. lia.
Qed.

Definition comp_env (P : list (list (list nity))) (i : nat) : environment :=
  map (fun row => nth i row nil) P.

Lemma nth_comp_env : forall (P : list (list (list nity))) i x,
  nth x (comp_env P i) nil = nth i (nth x P nil) nil.
Proof.
  intros P. induction P as [| row P IH]; intros i x.
  - unfold comp_env. simpl. destruct x; destruct i; reflexivity.
  - destruct x as [| x]; simpl.
    + reflexivity.
    + apply IH.
Qed.

Lemma map_nth_id : forall (l : list (list nity)),
  map (fun i => nth i l nil) (seq 0 (length l)) = l.
Proof.
  induction l as [| a l IH]; simpl.
  - reflexivity.
  - rewrite <- (seq_shift (length l) 0). rewrite map_map.
    change (a :: map (fun i => nth i l nil) (seq 0 (length l)) = a :: l).
    rewrite IH. reflexivity.
Qed.

Lemma concat_transpose : forall (P : list (list (list nity))) x,
  concat (map (fun i => nth x (comp_env P i) nil)
              (seq 0 (length (nth x P nil))))
  = concat (nth x P nil).
Proof.
  intros P x.
  assert (Hmap : map (fun i => nth x (comp_env P i) nil)
                     (seq 0 (length (nth x P nil)))
               = map (fun i => nth i (nth x P nil) nil)
                     (seq 0 (length (nth x P nil)))).
  { apply map_ext. intro i. apply nth_comp_env. }
  rewrite Hmap. rewrite map_nth_id. reflexivity.
Qed.

Lemma nth_EDs : forall (Parts : list (list (list nity))) (Ds : list environment) j,
  j < length Ds ->
  nth j (map (fun i => comp_env Parts (S i)) (seq 0 (length Ds))) nil
  = comp_env Parts (S j).
Proof.
  intros Parts Ds j Hj.
  rewrite (nth_map_lt nat environment (fun i => comp_env Parts (S i))
             (seq 0 (length Ds)) j nil 0).
  - rewrite nth_seq_0; [reflexivity | exact Hj].
  - rewrite length_seq. exact Hj.
Qed.

Lemma Forall2_map_seq : forall (l : list nity) (f : nat -> environment)
    (P : nity -> environment -> Prop),
  (forall i a, nth_error l i = Some a -> P a (f i)) ->
  Forall2 P l (map f (seq 0 (length l))).
Proof.
  induction l as [| a l IH]; intros f P H.
  - simpl. constructor.
  - simpl. rewrite <- (seq_shift (length l) 0). rewrite map_map.
    constructor.
    + apply H with (i := 0). reflexivity.
    + apply IH with (f := fun i => f (S i)).
      intros i b Hb. apply H with (i := S i). simpl. exact Hb.
Qed.

Definition ndef : nity := niatom 0.

Lemma cons_EDs : forall (Parts : list (list (list nity))) (k : nat),
  comp_env Parts 0 :: map (fun i => comp_env Parts (S i)) (seq 0 k)
  = map (fun i => comp_env Parts i) (seq 0 (S k)).
Proof.
  intros Parts k. rewrite <- (cons_seq k 0). simpl.
  rewrite <- (seq_shift k 0). rewrite map_map. reflexivity.
Qed.

Lemma nitlc_mono : forall M, forall G A, nitlc G M A ->
  forall E, length G = length E -> eincl G E -> nitlc E M A.
Proof.
  induction M as [x | M1 IH1 M2 IH2 | t0 M0 IH0].
  - intros G A H E Hlen He.
    inversion H as [t x' A' Hssim Hin | Gp Ds N1 N2 u A' Hperm Hfun Hargs
                   | t' M' u A' Hssim Hbody]; subst.
    apply nitlc_var with (t := t); [exact Hssim |].
    exact (incl_in (nth x G nil) (nth x E nil) A (He x) Hin).
  - intros G A H E Hlen He.
    inversion H as [t x' A' Hssim Hin | Gp Ds N1 N2 u A' Hperm Hfun Hargs
                   | t' M' u A' Hssim Hbody]; subst.
    (* normalization of all subderivations to length (length G) *)
    assert (HlenE : length E = length G) by (symmetry; exact Hlen).
    assert (HnbGp : nil_beyond (length G) Gp).
    { intros y Hy. apply (nth_nil_of_perm_nil G (Gp :: Ds) y Hperm).
      - apply nth_overflow. exact Hy.
      - left; reflexivity. }
    assert (HnbDs : forall D, In D Ds -> nil_beyond (length G) D).
    { intros D HD y Hy. apply (nth_nil_of_perm_nil G (Gp :: Ds) y Hperm).
      - apply nth_overflow. exact Hy.
      - right; exact HD. }
    set (Gpn := norm (length G) Gp).
    set (Dsn := map (fun D => norm (length G) D) Ds).
    assert (Hfunn : nitlc Gpn M1 (niarr u A)).
    { apply (nitlc_norm (length G) Gp M1 (niarr u A)); [exact HnbGp | exact Hfun]. }
    assert (Hargsn : Forall2 (fun B D => nitlc D M2 B) u Dsn).
    { assert (Hgen : forall (u0 : list nity) (Ds0 : list environment),
          Forall2 (fun B D => nitlc D M2 B) u0 Ds0 ->
          (forall D, In D Ds0 -> nil_beyond (length G) D) ->
          Forall2 (fun B D => nitlc D M2 B) u0
                  (map (fun D => norm (length G) D) Ds0)).
      { intros u0. induction u0 as [| b u']; intros Ds0 Hfa Hnb.
        - inversion Hfa. simpl. constructor.
        - destruct Ds0 as [| D Ds0].
          + inversion Hfa.
          + inversion Hfa as [| b' D' u'' Ds'' Hb Htl]; subst. simpl. constructor.
            * apply (nitlc_norm (length G) D M2 b (Hnb D (or_introl eq_refl)) Hb).
            * apply IHu'. exact Htl. intros E0 HE0. apply Hnb. right. exact HE0. }
      apply (Hgen u Ds Hargs). intros D HD. apply HnbDs. exact HD. }
    (* the inclusion premise for the row splitting *)
    assert (Hprem : forall y, y < length G ->
      incl (nth y Gpn nil ++ concat (map (fun D => nth y D nil) Dsn))
           (nth y E nil)).
    { intros y Hy.
      pose proof (Hperm y) as HP. simpl in HP. rewrite app_nil_r in HP.
      assert (HGpn : nth y Gpn nil = nth y Gp nil).
      { apply nth_norm_lt. exact Hy. }
      assert (HDsn : map (fun D => nth y D nil) Dsn
                   = map (fun D => nth y D nil) Ds).
      { unfold Dsn. rewrite map_map. apply map_ext. intro D. apply nth_norm_lt. exact Hy. }
      rewrite HGpn, HDsn.
      exact (incl_of_perm (nth y G nil)
               (nth y Gp nil ++ concat (map (fun D => nth y D nil) Ds))
               (nth y E nil) HP (He y)). }
    destruct (parts_exists (length G) E (fun y => nth y Gpn nil)
                (fun y => map (fun D => nth y D nil) Dsn) HlenE Hprem)
      as [Parts [HPlen HParts]].
    set (Ef := comp_env Parts 0).
    set (EDs := map (fun i => comp_env Parts (S i)) (seq 0 (length Ds))).
    assert (HlenEf : length Gpn = length Ef).
    { unfold Gpn. rewrite length_norm. unfold Ef, comp_env. rewrite length_map. rewrite HPlen. reflexivity. }
    assert (HeEf : eincl Gpn Ef).
    { intros y. destruct (Nat.lt_ge_cases y (length G)) as [Hy | Hy].
      - assert (HFa : Forall2 incl
            (nth y Gpn nil :: map (fun D => nth y D nil) Dsn) (nth y Parts nil))
          by (apply (proj2 (HParts y Hy))).
        unfold Ef. rewrite nth_comp_env.
        change (incl (nth 0 (nth y Gpn nil :: map (fun D => nth y D nil) Dsn) nil)
                     (nth 0 (nth y Parts nil) nil)).
        apply Forall2_incl_nth_i; [exact HFa | simpl; lia].
      - assert (HEfnil : nth y Ef nil = nil).
        { unfold Ef. rewrite nth_comp_env.
          assert (Hpy : nth y Parts nil = nil).
          { apply nth_overflow. rewrite HPlen. exact Hy. }
          rewrite Hpy. simpl. reflexivity. }
        rewrite HEfnil. unfold Gpn. rewrite (nth_norm_ge (length G) Gp y Hy). apply incl_refl. }
    assert (HfunE : nitlc Ef M1 (niarr u A)).
    { apply (IH1 Gpn (niarr u A) Hfunn Ef HlenEf HeEf). }
    (* argument typings at the transposed environments *)
    assert (HlenDsn : length Dsn = length Ds) by (unfold Dsn; apply length_map).
    assert (Hlen_uD : length u = length Ds).
    { rewrite (Forall2_length Hargsn). exact HlenDsn. }
    assert (HargsED : Forall2 (fun B D => nitlc D M2 B) u EDs).
    { unfold EDs. rewrite <- Hlen_uD.
      apply (Forall2_map_seq u (fun i => comp_env Parts (S i))
               (fun B D => nitlc D M2 B)).
      intros i a Hai.
      assert (Hi : i < length u) by (apply nth_error_Some; rewrite Hai; discriminate).
      assert (HiDs : i < length Ds) by (rewrite <- Hlen_uD; exact Hi).
      assert (Ha_eq : nth i u ndef = a) by (apply (nth_error_nth u i ndef Hai)).
      assert (Hni : nth i Dsn nil = norm (length G) (nth i Ds nil)).
      { unfold Dsn. rewrite (nth_map_lt environment environment
          (fun D => norm (length G) D) Ds i nil nil); [reflexivity | exact HiDs]. }
      assert (Hderiv : nitlc (nth i Dsn nil) M2 (nth i u ndef)).
      { apply (Forall2_nth nity environment (fun B D => nitlc D M2 B) u Dsn Hargsn
                 i (nth i u ndef) (nth i Dsn nil)).
        - rewrite <- Ha_eq in Hai. exact Hai.
        - apply nth_error_nth'. rewrite HlenDsn. exact HiDs. }
      assert (Hlen_i : length (nth i Dsn nil) = length (comp_env Parts (S i))).
      { rewrite Hni, length_norm. unfold comp_env. rewrite length_map. rewrite HPlen. reflexivity. }
      assert (He_i : eincl (nth i Dsn nil) (comp_env Parts (S i))).
      { intros y. destruct (Nat.lt_ge_cases y (length G)) as [Hy | Hy].
        - rewrite Hni. rewrite (nth_norm_lt (length G) (nth i Ds nil) y Hy).
          rewrite nth_comp_env.
          assert (HFa : Forall2 incl
              (nth y Gpn nil :: map (fun D => nth y D nil) Dsn) (nth y Parts nil))
            by (apply (proj2 (HParts y Hy))).
          assert (HSi : S i < length (nth y Gpn nil :: map (fun D => nth y D nil) Dsn)).
          { simpl. rewrite length_map. rewrite HlenDsn. lia. }
          pose proof (Forall2_incl_nth_i _ _ (S i) HFa HSi) as Hinc.
          simpl in Hinc.
          rewrite (nth_map_lt environment (list nity) (fun D => nth y D nil) Dsn i nil nil)
            in Hinc by (rewrite HlenDsn; exact HiDs).
          rewrite Hni in Hinc.
          rewrite (nth_norm_lt (length G) (nth i Ds nil) y Hy) in Hinc.
          exact Hinc.
        - rewrite Hni, (nth_norm_ge (length G) (nth i Ds nil) y Hy).
          rewrite nth_comp_env.
          assert (Hpy : nth y Parts nil = nil).
          { apply nth_overflow. rewrite HPlen. exact Hy. }
          rewrite Hpy. simpl. apply incl_refl. }
      rewrite <- Ha_eq.
      exact (IH2 (nth i Dsn nil) (nth i u ndef) Hderiv
               (comp_env Parts (S i)) Hlen_i He_i). }
    apply nitlc_app with (Gamma' := Ef) (Deltas := EDs) (u := u) (A := A).
    + intros y. destruct (Nat.lt_ge_cases y (length G)) as [Hy | Hy].
      * destruct (HParts y Hy) as [HEperm _].
        assert (HFa : Forall2 incl
            (nth y Gpn nil :: map (fun D => nth y D nil) Dsn) (nth y Parts nil))
          by (apply (proj2 (HParts y Hy))).
        assert (Hrowlen : length (nth y Parts nil) = S (length Ds)).
        { rewrite <- (Forall2_length HFa). simpl. rewrite length_map. rewrite HlenDsn. reflexivity. }
        unfold Ef, EDs. rewrite (cons_EDs Parts (length Ds)). rewrite map_map.
        rewrite <- Hrowlen. rewrite (concat_transpose Parts y).
        try (simpl; rewrite app_nil_r). exact HEperm.
      * assert (HEnil : nth y E nil = nil) by (apply nth_overflow; rewrite HlenE; exact Hy).
        simpl. rewrite app_nil_r. rewrite HEnil.
        assert (HEfnil : nth y Ef nil = nil).
        { unfold Ef. rewrite nth_comp_env.
          assert (Hpy : nth y Parts nil = nil).
          { apply nth_overflow. rewrite HPlen. exact Hy. }
          rewrite Hpy. simpl. reflexivity. }
        assert (HEDsnil : forall D, In D EDs -> nth y D nil = nil).
        { intros D HD. unfold EDs in HD. apply in_map_iff in HD.
          destruct HD as [j [Hjeq Hj]]. subst D. rewrite nth_comp_env.
          assert (Hpy : nth y Parts nil = nil).
          { apply nth_overflow. rewrite HPlen. exact Hy. }
          rewrite Hpy. simpl. reflexivity. }
        assert (Hmapnil : map (fun D => nth y D nil) EDs
                        = map (fun _ : environment => (@nil nity)) EDs).
        { apply map_ext_in. intros D HD. apply HEDsnil. exact HD. }
        simpl. rewrite HEfnil. simpl. rewrite Hmapnil, concat_map_nil_env.
        apply Permutation_refl.
    + exact HfunE.
    + exact HargsED.
  - intros G A H E Hlen He.
    inversion H as [t x' A' Hssim Hin | Gp Ds N1 N2 u A' Hperm Hfun Hargs
                   | t' M' u A' Hssim Hbody]; subst.
    apply nitlc_lam with (t := t0) (u := u) (A := A').
    + exact Hssim.
    + apply (IH0 (cons u G) A' Hbody (cons u E)).
      * simpl. rewrite Hlen. reflexivity.
      * intros y. destruct y as [| y]; simpl.
        -- apply incl_refl.
        -- apply He.
Qed.

(* Padding a lambda's binder entry is sound whenever the old entry is a
   sub-multiset of the new one and the new target is ssim of the same
   function type.  This is the rigid form of binder-entry inflation used
   by the checking/synthesis design; it follows from nitlc_mono because
   the binder entry is just the head of the body's environment. *)

Lemma nitlc_lam_pad : forall t M u A v Gamma,
  ssim t (niarr v A) ->
  nitlc (cons u Gamma) M A ->
  incl u v ->
  nitlc Gamma (lam t M) (niarr v A).
Proof.
  intros t M u A v Gamma Hssim Hbody Hincl.
  apply nitlc_lam with (t := t) (u := v) (A := A); [exact Hssim |].
  apply (nitlc_mono M (cons u Gamma) A Hbody (cons v Gamma)).
  - simpl. reflexivity.
  - intros x. destruct x as [| x]; simpl.
    + exact Hincl.
    + apply incl_refl.
Qed.

(* Append-only padding of a binder entry, the form used when a synthesis
   discovers extra demanded occurrence types after the body has been
   typed. *)

Lemma nitlc_lam_pad_app : forall t M u A w Gamma,
  ssim t (niarr (u ++ w) A) ->
  nitlc (cons u Gamma) M A ->
  nitlc Gamma (lam t M) (niarr (u ++ w) A).
Proof.
  intros t M u A w Gamma Hssim Hbody.
  apply (nitlc_lam_pad t M u A (u ++ w) Gamma Hssim Hbody).
  exists [], w. simpl. apply Permutation_refl.
Qed.

(* Combined form: pad the binder entry and enlarge the tail environment
   simultaneously, while preserving the lambda's target type. *)

Lemma nitlc_lam_pad_env : forall t M u A v Gamma Gamma',
  ssim t (niarr v A) ->
  nitlc (cons u Gamma) M A ->
  incl u v ->
  length Gamma = length Gamma' ->
  eincl Gamma Gamma' ->
  nitlc Gamma' (lam t M) (niarr v A).
Proof.
  intros t M u A v Gamma Gamma' Hssim Hbody Hincl Hlen He.
  apply nitlc_lam with (t := t) (u := v) (A := A); [exact Hssim |].
  apply (nitlc_mono M (cons u Gamma) A Hbody (cons v Gamma')).
  - simpl. rewrite Hlen. reflexivity.
  - intros x. destruct x as [| x]; simpl.
    + exact Hincl.
    + apply He.
Qed.

(* Sharing a common binder entry: two typings of the same term whose
   innermost binder entries are u and v can both be re-typed under any
   common entry W containing u and v (and under a common tail), by
   pointwise environment enlargement.  This is the tool that lets paired
   lambda bodies be typed with one common argument list. *)

Lemma nitlc_share_head : forall M A B u v G1 G2 W E,
  nitlc (cons u G1) M A ->
  nitlc (cons v G2) M B ->
  incl u W -> incl v W ->
  length G1 = length E -> length G2 = length E ->
  eincl G1 E -> eincl G2 E ->
  nitlc (cons W E) M A /\ nitlc (cons W E) M B.
Proof.
  intros M A B u v G1 G2 W E HA HB Hu Hv Hl1 Hl2 He1 He2. split.
  - apply (nitlc_mono M (cons u G1) A HA (cons W E)).
    + simpl. rewrite Hl1. reflexivity.
    + intros x. destruct x as [| x]; simpl.
      * exact Hu.
      * apply He1.
  - apply (nitlc_mono M (cons v G2) B HB (cons W E)).
    + simpl. rewrite Hl2. reflexivity.
    + intros x. destruct x as [| x]; simpl.
      * exact Hv.
      * apply He2.
Qed.

(* Bundled interface to the deterministic join: the join of two types of
   the same simple type is a common nle2 upper bound and is again ssim of
   that simple type. *)

Lemma jn_common : forall s A B,
  ssim s A -> ssim s B ->
  nle2 A (jn s A B) /\ nle2 B (jn s A B) /\ ssim s (jn s A B).
Proof.
  intros s A B HA HB. split; [apply (jn_nle2_left s A B HA HB) | split].
  - apply (jn_nle2_right s A B HA HB).
  - apply (jn_ssim s A B HA HB).
Qed.

Theorem nitlc_type_inference M Gamma0 t : stlc Gamma0 M t ->
  exists Gamma A,
    nitlc Gamma M A /\
    Forall2 (fun s u => u <> [] /\ Forall (ssim s) u) Gamma0 Gamma /\
    ssim t A.
