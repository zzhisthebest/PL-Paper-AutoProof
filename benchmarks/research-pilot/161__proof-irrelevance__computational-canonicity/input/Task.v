From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.

From AccInSProp Require Import core unscoped AST SubstNotations Util BasicAST Typing Reduction.

From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import CombineNotations.

Reserved Notation "t ---> u" (at level 50, u at next level).

Fixpoint mk_Nat k := match k with | 0 => zero | S k => succ (mk_Nat k) end.

Definition Box := Nat.

Definition boxlvl := prop.

Definition appu t u := app boxlvl boxlvl Box Box t u.

Definition lamu t := lam boxlvl boxlvl Box Box t.

Definition recu P pzero psucc t := rec boxlvl P pzero psucc t.

Definition accelu P p a := accel boxlvl boxlvl Box Box P p a Box.

Definition castu A B t := cast boxlvl A B Box t.

Definition Piu A B := Pi boxlvl boxlvl A B.

Definition accu A R a := acc boxlvl A R a.

Definition obsequ A a b := obseq boxlvl A a b.

Fixpoint erasure t :=
    match t with
    | var i => var i
    | assm c => assm c
    | lam _ _ _ _ t => lamu (erasure t)
    | app _ _ _ _ t u => appu (erasure t) (erasure u)
    | Pi _ _ A B => Piu (erasure A) (erasure B)
    | zero => zero
    | succ t => succ (erasure t)
    | rec _ P pzero psucc t =>
        recu (erasure P) (erasure pzero) (erasure psucc) (erasure t)
    | Nat => Nat
    | accel _ _ _ _ P p a _ =>
        accelu (erasure P) (erasure p) (erasure a)
    | Sort i => Sort i
    | acc _ A R a => accu (erasure A) (erasure R) (erasure a)
    | obseq _ A a b => obsequ (erasure A) (erasure a) (erasure b)
    | cast i A B e t => castu (erasure A) (erasure B) (erasure t)
    | _ => Nat
    end.

Inductive red_untyped : term -> term -> Prop :=
| redu_app t t' u :
    t ---> t' ->
    appu t u ---> appu t' u

| redu_beta t u :
    appu (lamu t) u ---> t <[ u.. ]

| redu_rec P p_zero p_succ n n' :
    n ---> n' ->
    recu P p_zero p_succ n ---> recu P p_zero p_succ n'

| redu_rec_zero P p_zero p_succ :
    recu P p_zero p_succ zero ---> p_zero

| redu_rec_succ P p_zero p_succ n :
    recu P p_zero p_succ (succ n) ---> p_succ <[  (recu P p_zero p_succ n) .: n ..]

| redu_accel a P p :
    let Pwk := (up_ren (S >> S)) ⋅ P in
    let pwk := (up_ren (up_ren (S >> S))) ⋅ p in
    let t1 := accelu Pwk pwk (var 1) in
    let t3 := lamu t1 in
    let t5 := lamu t3 in
    accelu P p a ---> p <[ t5 .: a ..]

| redu_cast1 A A' B a :
    A ---> A' ->
    castu A B a ---> castu A' B a

| redu_cast2 A B B' a :
    val A ->
    B ---> B' ->
    castu A B a ---> castu A B' a

| redu_cast_nat t :
    castu Nat Nat t ---> t

| redu_cast_sort i t :
    castu (Sort i) (Sort i) t ---> t

| redu_cast_pi A1 A2 B1 B2 f :
    let A1' := S ⋅ A1 in
    let A2' := S ⋅ A2 in
    let t1 := castu A2' A1' (var 0) in
    let t2 := appu (S ⋅ f) t1 in
    let t3 := castu (B1 <[t1.: S >> var]) B2 t2 in
    let t4 := lamu t3 in
    castu (Piu A1 B1) (Piu A2 B2) f ---> t4

where "t ---> u" := (red_untyped t u).

Reserved Notation "t -->> u" (at level 50, u at next level).

Inductive reddu : term -> term -> Prop :=
  | reddu_refl t : t -->> t
  | reddu_step t u v : t ---> v -> v -->> u -> t -->> u
where "t -->> t'" := (reddu t t').

Inductive eval : term -> nat -> Prop :=
| eval_0 t :
    t -->> zero ->
    eval t 0
| eval_S t u n :
    t -->> succ u ->
    eval u n ->
    eval t (S n).

(* Assumptions A and B of the original development. *)
Parameter nat_neq_sort : forall e, ∙ ⊢d< prop > e : obseq (ty 1) (Sort (ty 0)) Nat (Sort prop) -> False.
Parameter nat_neq_pi  : forall i j A B e, ∙ ⊢d< prop > e : obseq (ty 1) (Sort (ty 0)) Nat (Pi i j A B) -> False.
Parameter sort_neq_pi  : forall l i j A B e, ∙ ⊢d< prop > e : obseq (Ax (Ax l)) (Sort (Ax l)) (Sort l) (Pi i j A B) -> False.
(* The following axiom is equivalent to the fact that, if the two function types have different heads, we get a contradiction *)
Parameter pi_sort_inj : forall i n i' n' A A' B B' e,
    Ru i (ty n) = Ru i' (ty n') ->
    ∙ ⊢d< prop > e : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A B) (Pi i' (ty n') A' B') ->
    i = i' /\ n = n'.


Definition meta l A R (t u : { x : term | ∙ ⊢d< l > x : A})
  := ∃ p, ∙ ⊢d< prop > p : R <[(proj1_sig u) .: (proj1_sig t) ..].

Parameter ob_to_meta : forall n A R a e, ∙ ⊢d< prop > e : acc (ty n) A R (proj1_sig a) -> Acc (meta (ty n) A R) a.

Theorem computational_canonicity n :
    ∙ ⊢d< ty 0 > n : Nat ->
    exists k, eval (erasure n) k /\
    ∙ ⊢d< ty 0 > n ≡ mk_Nat k : Nat /\
    (forall k', eval (erasure n) k' -> k = k').
