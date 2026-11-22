Require Import SSTS CD Reduction.
Require Import L.
From Stdlib Require Import List.
Import ListNotations.
Import L.

(* ------------------------------------------------------------------ *)
(* Verified infrastructure for the reduction (the target statement is *)
(* unchanged; these are helper definitions and lemmas only).          *)
(* ------------------------------------------------------------------ *)

(* The right-nested continuation type of a word, with end atom [Z]. *)
Definition word_ty (Z : sty) (w : list nat) : sty :=
  fold_right (fun a t => arr (atom a) [] t) Z w.

(* The type assigned to a rule variable for the rule [a b -> c d]: it
   can be used as a backward continuation transformer for the pair, and
   its second intersection member yields the second output symbol. *)
Definition rule_ty (a b c d : nat) : ty :=
  (arr (atom a) [] (arr (atom b) [] (atom c)),
   [arr (atom a) [] (arr (atom b) [] (atom d))]).

(* Backward one-step transformer: given a continuation of the new word
   [c d v], build one for the old word [a b v].  It is uniform in the
   tail [v]. *)
Definition step_term : term :=
  lam (lam (lam
    (app (app (var 2)
              (app (app (var 3) (var 1)) (var 0)))
         (app (app (var 3) (var 1)) (var 0))))).

Ltac tv x S P T :=
  eapply type_assignment_var with (s := S) (phi := P) (t := T);
  [ cbn; reflexivity | cbn; auto ].

Lemma step_term_ty (Z : sty) (a b c d : nat) (v : list nat) :
  type_assignment [rule_ty a b c d] step_term
    (arr (word_ty Z (c :: d :: v)) [] (word_ty Z (a :: b :: v))).
Proof.
  unfold step_term, word_ty, rule_ty. cbn.
  eapply type_assignment_arr.
  eapply type_assignment_arr.
  eapply type_assignment_arr.
  eapply type_assignment_app with (s := atom d) (phi := (@nil sty)).
  - eapply type_assignment_app with (s := atom c) (phi := (@nil sty)).
    + tv 2 (arr (atom c) (@nil sty) (arr (atom d) (@nil sty) (word_ty Z v)))
         (@nil sty)
         (arr (atom c) (@nil sty) (arr (atom d) (@nil sty) (word_ty Z v))).
    + eapply type_assignment_app with (s := atom b) (phi := (@nil sty)).
      * eapply type_assignment_app with (s := atom a) (phi := (@nil sty)).
        -- tv 3 (arr (atom a) (@nil sty) (arr (atom b) (@nil sty) (atom c)))
                 [arr (atom a) (@nil sty) (arr (atom b) (@nil sty) (atom d))]
                 (arr (atom a) (@nil sty) (arr (atom b) (@nil sty) (atom c))).
        -- tv 1 (atom a) (@nil sty) (atom a).
        -- constructor.
      * tv 0 (atom b) (@nil sty) (atom b).
      * constructor.
    + constructor.
  - eapply type_assignment_app with (s := atom b) (phi := (@nil sty)).
    * eapply type_assignment_app with (s := atom a) (phi := (@nil sty)).
      -- tv 3 (arr (atom a) (@nil sty) (arr (atom b) (@nil sty) (atom c)))
               [arr (atom a) (@nil sty) (arr (atom b) (@nil sty) (atom d))]
               (arr (atom a) (@nil sty) (arr (atom b) (@nil sty) (atom d))).
      -- tv 1 (atom a) (@nil sty) (atom a).
      -- constructor.
    * tv 0 (atom b) (@nil sty) (atom b).
    * constructor.
  - constructor.
Qed.

(* ------------------------------------------------------------------ *)
(* Verified "counters as nested types" infrastructure.  A counter value
   [n] is represented by [Nt n]; [Nt 0] is the base atom and each
   successor adds one arrow.  These transformers are uniform in [n],
   which is the mechanism that would let an inhabitant choose unbounded
   data.  They are recorded here as verified building blocks.          *)
(* ------------------------------------------------------------------ *)

Fixpoint Nt (n : nat) : sty :=
  match n with
  | 0 => atom 0
  | S k => arr (atom 1) [] (Nt k)
  end.

Definition K (n : nat) (X : sty) : sty := arr (Nt n) [] X.

(* increment: K (S n) -> K n *)
Definition inc_term : term := lam (lam (app (var 1) (lam (var 1)))).

Lemma inc_term_ty (n : nat) (X : sty) :
  type_assignment (@nil ty) inc_term (arr (K (S n) X) [] (K n X)).
Proof.
  unfold inc_term, K, Nt. cbn.
  eapply type_assignment_arr.
  eapply type_assignment_arr.
  eapply type_assignment_app with (s := Nt (S n)) (phi := (@nil sty)).
  - tv 1 (arr (Nt (S n)) (@nil sty) X) (@nil sty)
       (arr (Nt (S n)) (@nil sty) X).
  - eapply type_assignment_arr.
    tv 1 (Nt n) (@nil sty) (Nt n).
  - constructor.
Qed.

(* decrement: from a source [s0 : atom 1], K n -> K (S n) *)
Definition dec_term : term := lam (lam (app (var 1) (app (var 0) (var 2)))).

Lemma dec_term_ty (n : nat) (X : sty) :
  type_assignment [(atom 1, (@nil sty))] dec_term
    (arr (K n X) [] (K (S n) X)).
Proof.
  unfold dec_term, K, Nt. cbn.
  eapply type_assignment_arr.
  eapply type_assignment_arr.
  eapply type_assignment_app with (s := Nt n) (phi := (@nil sty)).
  - tv 1 (arr (Nt n) (@nil sty) X) (@nil sty) (arr (Nt n) (@nil sty) X).
  - eapply type_assignment_app with (s := atom 1) (phi := (@nil sty)).
    + tv 0 (arr (atom 1) (@nil sty) (Nt n)) (@nil sty)
         (arr (atom 1) (@nil sty) (Nt n)).
    + tv 2 (atom 1) (@nil sty) (atom 1).
    + constructor.
  - constructor.
Qed.

(* zero test: the "is zero" branch transforms [K 0 X] into [K 0 X].
   Together with [dec_term_ty] (the non-zero branch [K n X] -> [K (S n) X])
   this is the type-level zero/non-zero discrimination. *)
Definition zb_term : term := lam (lam (app (var 1) (var 0))).

Lemma zb_term_ty (X : sty) :
  type_assignment (@nil ty) zb_term (arr (K 0 X) [] (K 0 X)).
Proof.
  unfold zb_term, K, Nt. cbn.
  eapply type_assignment_arr. eapply type_assignment_arr.
  eapply type_assignment_app with (s := atom 0) (phi := (@nil sty)).
  - tv 1 (arr (atom 0) (@nil sty) X) (@nil sty) (arr (atom 0) (@nil sty) X).
  - tv 0 (atom 0) (@nil sty) (atom 0).
  - constructor.
Qed.

(* ------------------------------------------------------------------ *)
(* Verified position-tagging mechanism.  A word position carries both a
   symbol function [T_i -> atom s_i] and a tag term [: T_i].  A rule
   rewrites the symbol functions while threading the tag types unchanged.
   This is the key device that makes positions distinguishable (the tags
   occur in the *domains* of the symbol functions).                       *)
(* ------------------------------------------------------------------ *)

Definition C2 (x y : nat) (T1 T2 Z : sty) : sty :=
  arr (arr T1 [] (atom x)) []
      (arr T1 []
           (arr (arr T2 [] (atom y)) []
                (arr T2 [] Z))).

Definition Gr (a b c d : nat) : list ty :=
  [(arr (atom a) [] (arr (atom b) [] (atom c)), (@nil sty));
   (arr (atom a) [] (arr (atom b) [] (atom d)), (@nil sty))].

Definition tag_step (a b c d : nat) : term :=
  lam (lam (lam (lam (lam
    (app
      (app
        (app
          (app (var 4)
               (lam (app (app (var 6) (app (var 4) (var 0)))
                          (app (var 2) (var 1)))))
          (var 2))
        (lam (app (app (var 7) (app (var 4) (var 3)))
                   (app (var 2) (var 0)))))
      (var 0)))))).

Lemma tag_step_ty (a b c d : nat) (T1 T2 Z : sty) :
  type_assignment (Gr a b c d) (tag_step a b c d)
    (arr (C2 c d T1 T2 Z) [] (C2 a b T1 T2 Z)).
Proof.
  unfold tag_step, C2, Gr. cbn.
  eapply type_assignment_arr.
  eapply type_assignment_arr.
  eapply type_assignment_arr.
  eapply type_assignment_arr.
  eapply type_assignment_arr.
  eapply type_assignment_app with (s := T2) (phi := (@nil sty)).
  - eapply type_assignment_app with (s := arr T2 [] (atom d)) (phi := (@nil sty)).
    + eapply type_assignment_app with (s := T1) (phi := (@nil sty)).
      * eapply type_assignment_app with (s := arr T1 [] (atom c)) (phi := (@nil sty)).
        -- tv 4 (arr (arr T1 [] (atom c)) (@nil sty)
                    (arr T1 [] (arr (arr T2 [] (atom d)) (@nil sty) (arr T2 [] Z))))
                 (@nil sty)
                 (arr (arr T1 [] (atom c)) (@nil sty)
                    (arr T1 [] (arr (arr T2 [] (atom d)) (@nil sty) (arr T2 [] Z)))).
        -- eapply type_assignment_arr.
           eapply type_assignment_app with (s := atom b) (phi := (@nil sty)).
           ++ eapply type_assignment_app with (s := atom a) (phi := (@nil sty)).
              ** tv 6 (arr (atom a) (@nil sty) (arr (atom b) (@nil sty) (atom c))) (@nil sty)
                       (arr (atom a) (@nil sty) (arr (atom b) (@nil sty) (atom c))).
              ** eapply type_assignment_app with (s := T1) (phi := (@nil sty)).
                 --- tv 4 (arr T1 (@nil sty) (atom a)) (@nil sty) (arr T1 (@nil sty) (atom a)).
                 --- tv 0 T1 (@nil sty) T1.
                 --- constructor.
              ** constructor.
           ++ eapply type_assignment_app with (s := T2) (phi := (@nil sty)).
              ** tv 2 (arr T2 (@nil sty) (atom b)) (@nil sty) (arr T2 (@nil sty) (atom b)).
              ** tv 1 T2 (@nil sty) T2.
              ** constructor.
           ++ constructor.
        -- constructor.
      * tv 2 T1 (@nil sty) T1.
      * constructor.
    + eapply type_assignment_arr.
      eapply type_assignment_app with (s := atom b) (phi := (@nil sty)).
      * eapply type_assignment_app with (s := atom a) (phi := (@nil sty)).
        -- tv 7 (arr (atom a) (@nil sty) (arr (atom b) (@nil sty) (atom d))) (@nil sty)
                 (arr (atom a) (@nil sty) (arr (atom b) (@nil sty) (atom d))).
        -- eapply type_assignment_app with (s := T1) (phi := (@nil sty)).
           ++ tv 4 (arr T1 (@nil sty) (atom a)) (@nil sty) (arr T1 (@nil sty) (atom a)).
           ++ tv 3 T1 (@nil sty) T1.
           ++ constructor.
        -- constructor.
      * eapply type_assignment_app with (s := T2) (phi := (@nil sty)).
        -- tv 2 (arr T2 (@nil sty) (atom b)) (@nil sty) (arr T2 (@nil sty) (atom b)).
        -- tv 0 T2 (@nil sty) T2.
        -- constructor.
      * constructor.
    + constructor.
  - tv 0 T2 (@nil sty) T2.
  - constructor.
Qed.

(* Single-position consumer and its canonical final-check / initial-zero
   terms.  [acc_term] is the final all-1 check; [zf_term] is the initial
   zero symbol function.  Both are fully verified.                      *)
Definition C1 (x : nat) (T Z : sty) : sty :=
  arr (arr T [] (atom x)) [] (arr T [] Z).

Definition acc_term : term := lam (lam (app (var 2) (app (var 1) (var 0)))).

Lemma acc_term_ty (T X : sty) :
  type_assignment [(arr (atom 1) [] X, (@nil sty))] acc_term (C1 1 T X).
Proof.
  unfold acc_term, C1. cbn.
  eapply type_assignment_arr. eapply type_assignment_arr.
  eapply type_assignment_app with (s := atom 1) (phi := (@nil sty)).
  - tv 2 (arr (atom 1) (@nil sty) X) (@nil sty) (arr (atom 1) (@nil sty) X).
  - eapply type_assignment_app with (s := T) (phi := (@nil sty)).
    + tv 1 (arr T (@nil sty) (atom 1)) (@nil sty) (arr T (@nil sty) (atom 1)).
    + tv 0 T (@nil sty) T.
    + constructor.
  - constructor.
Qed.

Definition zf_term : term := lam (var 1).

Lemma zf_term_ty (T : sty) :
  type_assignment [(atom 0, (@nil sty))] zf_term (arr T [] (atom 0)).
Proof.
  unfold zf_term. cbn.
  eapply type_assignment_arr.
  tv 1 (atom 0) (@nil sty) (atom 0).
Qed.

Theorem reduction : SSTS01 ⪯ CD_INH.
