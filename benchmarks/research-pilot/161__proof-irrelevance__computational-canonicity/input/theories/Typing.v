From Stdlib Require Import Utf8 List Arith Bool.

From AccInSProp Require Import core unscoped AST SubstNotations.

From AccInSProp Require Import Util BasicAST.

From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import ListNotations.

Import CombineNotations.

Open Scope subst_scope.

Definition ctx := list (level * term).

Notation "'∙'" :=
  (@nil (level * term)).

Notation "Γ ,, d" :=
  (@cons (level * term) d Γ) (at level 20, d at next level).

Notation "Γ ,,, Δ" :=
  (@List.app (level * term) Δ Γ) (at level 25, Δ at next level, left associativity).

Inductive mode := | mdef | mprop.

Parameter assm_sig : list term.

Reserved Notation "Γ ∋< l > x : T" (at level 50, l, x, T at next level).

Reserved Notation "Γ ▹ M ⊢< l > t : T" (at level 50, l, M, t, T at next level).

Reserved Notation "Γ ▹ M ⊢< l > t ≡ u : T" (at level 50, l, M, t, u, T at next level).

Reserved Notation "▹ M ⊢ Γ" (at level 50, Γ at next level).

Inductive varty : ctx → nat → level → term → Prop :=
| vartyO Γ l A : Γ ,, (l , A) ∋< l > 0 : S ⋅ A
| vartyS Γ i j A B x : Γ ∋< i > x : A → Γ ,, (j, B) ∋< i > S x : S ⋅ A

where "Γ ∋< l > x : T" := (varty Γ x l T).

Inductive typing M : ctx -> level -> term → term → Prop :=

| type_var :
    ∀ Γ x l A,
      ▹ M ⊢ Γ ->
      Γ ∋< l > x : A →
      Γ ▹ M ⊢< l > (var x) : A

| type_sort :
    ∀ Γ l,
      ▹ M ⊢ Γ ->
      Γ ▹ M ⊢< Ax (Ax l) > Sort l : Sort (Ax l)

| type_assm :
    ∀ Γ c A,
      ▹ M ⊢ Γ ->
      nth_error assm_sig c = Some A ->
      ∙ ▹ M ⊢< Ax prop > A : Sort prop ->
      Γ ▹ M ⊢< prop > assm c : A

| type_pi :
    ∀ Γ i j A B,
      Γ ▹ M ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ▹ M ⊢< Ax j > B : Sort j →
      Γ ▹ M ⊢< Ax (Ru i j) > Pi i j A B : Sort (Ru i j)


| type_lam :
    ∀ Γ i j A B t,
      Γ ▹ M ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ▹ M ⊢< Ax j > B : Sort j →
      Γ ,, (i , A) ▹ M ⊢< j > t : B →
      Γ ▹ M ⊢< Ru i j > lam i j A B t : Pi i j A B

| type_app :
    ∀ Γ i j A B t u,
      Γ ▹ M ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ▹ M ⊢< Ax j > B : Sort j →
      Γ ▹ M ⊢< Ru i j > t : Pi i j A B →
      Γ ▹ M ⊢< i > u : A →
      Γ ▹ M ⊢< j > app i j A B  t u : B <[ u .. ]

| type_nat :
    ∀ Γ,
      ▹ M ⊢ Γ ->
      Γ ▹ M ⊢< ty 1 > Nat : Sort (ty 0)

| type_zero :
    ∀ Γ,
      ▹ M ⊢ Γ ->
      Γ ▹ M ⊢< ty 0 > zero : Nat

| type_succ :
    ∀ Γ t,
      Γ ▹ M ⊢< ty 0 > t : Nat ->
      Γ ▹ M ⊢< ty 0 > succ t : Nat

| type_rec :
    ∀ Γ l P p_zero p_succ t,
      Γ ,, (ty 0 , Nat) ▹ M ⊢< Ax l > P : Sort l ->
      Γ ▹ M ⊢< l > p_zero : P <[ zero .. ] ->
      Γ ,, (ty 0 , Nat) ,, (l , P) ▹ M ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
      Γ ▹ M ⊢< ty 0 > t : Nat ->
      Γ ▹ M ⊢< l > rec l P p_zero p_succ t : P <[ t .. ]

| type_acc :
    ∀ Γ n A R a,
    Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop ->
    Γ ▹ M ⊢< ty n > a : A ->
    Γ ▹ M ⊢< Ax prop > acc (ty n) A R a : Sort prop

| type_accin :
    ∀ Γ n A R a p,
    Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop ->
    Γ ▹ M ⊢< ty n > a : A ->
    let A_wk := (S >> S) ⋅ A in
    let R_wk := (up_ren (up_ren (S >> S))) ⋅ R in
    let acc_wk := acc (ty n) A_wk R_wk (var 1)  in
    let R' := R <[(S ⋅ a) .: (var 0 .: (S >> var))] in
    Γ ▹ M ⊢< prop > p : Pi (ty n) prop A (Pi prop prop R' acc_wk) ->
    Γ ▹ M ⊢< prop > accin (ty n) A R a p : acc (ty n) A R a

| type_accinv :
    ∀ Γ n A R a p b r,
    Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop ->
    Γ ▹ M ⊢< ty n > a : A ->
    Γ ▹ M ⊢< prop > p : acc (ty n) A R a ->
    Γ ▹ M ⊢< ty n > b : A ->
    Γ ▹ M ⊢< prop > r : R <[a.:b..] ->
    Γ ▹ M ⊢< prop > accinv (ty n) A R a p b r : acc (ty n) A R b

| type_accel :
    ∀ Γ n l A R a q P p,
    Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop ->
    Γ ,, (ty n, A) ▹ M ⊢< Ax l > P : Sort l ->
    let R' := (1 .: (0 .: (S >> S))) ⋅ R in
    let P' := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi (ty n) l (S ⋅ A) (Pi prop l R' P') in
    let P'' := (1.: (S >> S)) ⋅ P in
    Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ▹ M ⊢< l > p : P'' ->
    Γ ▹ M ⊢< ty n > a : A ->
    Γ ▹ M ⊢< prop > q : acc (ty n) A R a ->
    Γ ▹ M ⊢< l > accel (ty n) l A R P p a q : P <[a ..]

| type_accelcomp :
    ∀ Γ n m A R a q P p,
    Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop ->
    Γ ,, (ty n, A) ▹ M ⊢< Ax (ty m) > P : Sort (ty m) ->
    let R' := (1 .: (0 .: (S >> S))) ⋅ R in
    let P' := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi (ty n) (ty m) (S ⋅ A) (Pi prop (ty m) R' P') in
    let P'' := (1.: (S >> S)) ⋅ P in
    Γ ,, (ty n, A) ,, (Ru (ty n) (ty m), B) ▹ M ⊢< ty m > p : P'' ->
    Γ ▹ M ⊢< ty n > a : A ->
    Γ ▹ M ⊢< prop > q : acc (ty n) A R a ->
    let Awk := (S >> S) ⋅ A in
    let Rwk := (up_ren (up_ren (S >> S))) ⋅ R in
    let Pwk := (up_ren (S >> S)) ⋅ P in
    let pwk := (up_ren (up_ren (S >> S))) ⋅ p in
    let t0 := accinv (ty n) Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0) in
    let t1 := accel (ty n) (ty m) Awk Rwk Pwk pwk (var 1) t0 in
    let t2 := R<[S ⋅ a .: (var 0 .: S >> var)] in
    let t3 := lam prop (ty m) t2 P'' t1 in
    let t4 := Pi prop (ty m) t2 P'' in
    let t5 := lam (ty n) (ty m) A t4 t3 in
    Γ ▹ M ⊢< prop > accelcomp (ty n) (ty m) A R P p a q : obseq (ty m) (P <[a ..]) (accel (ty n) (ty m) A R P p a q) (p <[ t5 .: a ..])

| type_obseq :
    ∀ Γ n A a b,
    Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ▹ M ⊢< ty n > a : A ->
    Γ ▹ M ⊢< ty n > b : A ->
    Γ ▹ M ⊢< Ax prop > obseq (ty n) A a b : Sort prop

| type_obsrefl :
    ∀ Γ n A a,
      Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
      Γ ▹ M ⊢< ty n > a : A ->
      Γ ▹ M ⊢< prop > obsrefl (ty n) A a : obseq (ty n) A a a

| type_J :
    ∀ Γ n A a P p b e,
      Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
      Γ ▹ M ⊢< ty n > a : A ->
      Γ ,, (ty n , A) ▹ M ⊢< Ax prop > P : Sort prop ->
      Γ ▹ M ⊢< prop > p : P <[a..] ->
      Γ ▹ M ⊢< ty n > b : A ->
      Γ ▹ M ⊢< prop > e : obseq (ty n) A a b ->
      Γ ▹ M ⊢< prop > J (ty n) A a P p b e : P <[b..]

| type_cast :
  ∀ Γ i A B e a,
    Γ ▹ M ⊢< Ax i > A : Sort i ->
    Γ ▹ M ⊢< Ax i > B : Sort i ->
    Γ ▹ M ⊢< prop > e : obseq (Ax i) (Sort i) A B ->
    Γ ▹ M ⊢< i > a : A ->
    Γ ▹ M ⊢< i > cast i A B e a : B

| type_injpi1 :
  ∀ Γ i n A1 A2 B1 B2 e,
    Γ ▹ M ⊢< Ax i > A1 : Sort i ->
    Γ ,, (i, A1) ▹ M ⊢< Ax (ty n) > B1 : Sort (ty n) ->
    Γ ▹ M ⊢< Ax i > A2 : Sort i ->
    Γ ,, (i, A2) ▹ M ⊢< Ax (ty n) > B2 : Sort (ty n) ->
    Γ ▹ M ⊢< prop > e : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ▹ M ⊢< prop > injpi1 i (ty n) A1 A2 B1 B2 e : obseq (Ax i) (Sort i) A2 A1

| type_injpi2 :
  ∀ Γ i n A1 A2 B1 B2 e a2,
    Γ ▹ M ⊢< Ax i > A1 : Sort i ->
    Γ ,, (i, A1) ▹ M ⊢< Ax (ty n) > B1 : Sort (ty n) ->
    Γ ▹ M ⊢< Ax i > A2 : Sort i ->
    Γ ,, (i, A2) ▹ M ⊢< Ax (ty n) > B2 : Sort (ty n) ->
    Γ ▹ M ⊢< prop > e : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ▹ M ⊢< i > a2 : A2 ->
    let a1 := cast i A2 A1 (injpi1 i (ty n) A1 A2 B1 B2 e) a2 in
    Γ ▹ M ⊢< prop > injpi2 i (ty n) A1 A2 B1 B2 e a2 : obseq (Ax (ty n)) (Sort (ty n)) (B1<[a1..]) (B2 <[a2..])

| type_conv :
    ∀ Γ l A B t,
      Γ ▹ M ⊢< l > t : A ->
      Γ ▹ M ⊢< Ax l > A ≡ B : Sort l ->
      Γ ▹ M ⊢< l > t : B

with ctx_typing M : ctx -> Prop :=
| ctx_nil :
      ▹ M ⊢ ∙

| ctx_cons :
    ∀ Γ l A,
      ▹ M ⊢ Γ ->
      Γ ▹ M ⊢< Ax l > A : Sort l ->
      ▹ M ⊢ (Γ ,, (l , A))

with conversion M : ctx -> level -> term -> term -> term -> Prop :=

| conv_var :
    ∀ Γ x l A,
      Γ ∋< l > x : A →
      ▹ M ⊢ Γ ->
      Γ ▹ M ⊢< l > var x ≡ var x : A

| conv_sort :
    ∀ Γ l,
      ▹ M ⊢ Γ ->
      Γ ▹ M ⊢< Ax (Ax l) > Sort l ≡ Sort l : Sort (Ax l)

| conv_assm :
    ∀ Γ c A,
      ▹ M ⊢ Γ ->
      nth_error assm_sig c = Some A ->
      ∙ ▹ M ⊢< Ax prop > A : Sort prop ->
      Γ ▹ M ⊢< prop > assm c ≡ assm c : A


| conv_pi :
    ∀ Γ i j A B A' B',
      Γ ▹ M ⊢< Ax i > A : Sort i →
      Γ ▹ M ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ▹ M ⊢< Ax j > B ≡ B' : Sort j →
      Γ ▹ M ⊢< Ax (Ru i j) > Pi i j A B ≡ Pi i j A' B' : Sort (Ru i j)

| conv_lam :
    ∀ Γ i j A B t A' B' t',
      Γ ▹ M ⊢< Ax i > A : Sort i →
      Γ ▹ M ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ▹ M ⊢< Ax j > B ≡ B': Sort j →
      Γ ,, (i , A) ▹ M ⊢< j > t ≡ t' : B →
      Γ ▹ M ⊢< Ru i j > lam i j A B t ≡ lam i j A' B' t' : Pi i j A B

| conv_app :
    ∀ Γ i j A B t u A' B' t' u',
      Γ ▹ M ⊢< Ax i > A : Sort i →
      Γ ▹ M ⊢< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ▹ M ⊢< Ax j > B ≡ B': Sort j →
      Γ ▹ M ⊢< Ru i j > t ≡ t' : Pi i j A B →
      Γ ▹ M ⊢< i > u : A →
      Γ ▹ M ⊢< i > u' : A' →
      Γ ▹ M ⊢< i > u ≡ u' : A →
      Γ ▹ M ⊢< j > app i j A B t u ≡ app i j A' B' t' u' : B <[ u .. ]


| conv_nat :
    ∀ Γ,
      ▹ M ⊢ Γ ->
      Γ ▹ M ⊢< ty 1 > Nat ≡ Nat : Sort (ty 0)

| conv_zero :
    ∀ Γ,
      ▹ M ⊢ Γ ->
      Γ ▹ M ⊢< ty 0 > zero ≡ zero : Nat

| conv_succ :
    ∀ Γ t t',
      Γ ▹ M ⊢< ty 0 > t ≡ t' : Nat ->
      Γ ▹ M ⊢< ty 0 > succ t ≡ succ t' : Nat

| conv_rec :
    ∀ Γ l P p_zero p_succ t P' p_zero' p_succ' t',
      Γ ,, (ty 0 , Nat) ▹ M ⊢< Ax l > P : Sort l ->
      Γ ,, (ty 0 , Nat) ▹ M ⊢< Ax l > P ≡ P' : Sort l ->
      Γ ▹ M ⊢< l > p_zero ≡ p_zero' : P <[ zero .. ] ->
      Γ ,, (ty 0 , Nat) ,, (l , P) ▹ M ⊢< l > p_succ ≡ p_succ' : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
      Γ ▹ M ⊢< ty 0 > t ≡ t' : Nat ->
      Γ ▹ M ⊢< l > rec l P p_zero p_succ t ≡ rec l P' p_zero' p_succ' t' : P <[ t .. ]


| conv_acc :
    ∀ Γ n A A' R R' a a',
    Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ▹ M ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R ≡ R' : Sort prop ->
    Γ ▹ M ⊢< ty n > a ≡ a' : A ->
    Γ ▹ M ⊢< Ax prop > acc (ty n) A R a ≡ acc (ty n) A' R' a' : Sort prop

| conv_accin :
    ∀ Γ n A A' R R' a a' p p',
    Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ▹ M ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R ≡ R' : Sort prop ->
    Γ ▹ M ⊢< ty n > a ≡ a' : A ->
    let A_wk := (S >> S) ⋅ A in
    let R_wk := (up_ren (up_ren (S >> S))) ⋅ R in
    let acc_wk := acc (ty n) A_wk R_wk (var 1)  in
    let RR := R <[(S ⋅ a) .: (var 0 .: (S >> var))] in
    Γ ▹ M ⊢< prop > p ≡ p' : Pi (ty n) prop A (Pi prop prop RR acc_wk) ->
    Γ ▹ M ⊢< prop > accin (ty n) A R a p ≡ accin (ty n) A' R' a' p' : acc (ty n) A R a

| conv_accinv :
    ∀ Γ n A A' R R' a a' p p' b b' r r',
    Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ▹ M ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R ≡ R' : Sort prop ->
    Γ ▹ M ⊢< ty n > a ≡ a' : A ->
    Γ ▹ M ⊢< prop > p ≡ p' : acc (ty n) A R a ->
    Γ ▹ M ⊢< ty n > b ≡ b' : A ->
    Γ ▹ M ⊢< prop > r ≡ r' : R <[a.:b..] ->
    Γ ▹ M ⊢< prop > accinv (ty n) A R a p b r ≡ accinv (ty n) A' R' a' p' b' r' : acc (ty n) A R b

| conv_accel :
    ∀ Γ n l A A' R R' a a' q q' P P' p p',
    Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ▹ M ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R ≡ R' : Sort prop ->
    Γ ,, (ty n, A) ▹ M ⊢< Ax l > P : Sort l ->
    Γ ,, (ty n, A) ▹ M ⊢< Ax l > P ≡ P' : Sort l ->
    let R_ := (1 .: (0 .: (S >> S))) ⋅ R in
    let P_ := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi (ty n) l (S ⋅ A) (Pi prop l R_ P_) in
    let P'' := (1.: (S >> S)) ⋅ P in
    Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ▹ M ⊢< l > p ≡ p' : P'' ->
    Γ ▹ M ⊢< ty n > a ≡ a': A ->
    Γ ▹ M ⊢< prop > q : acc (ty n) A R a ->
    Γ ▹ M ⊢< prop > q' : acc (ty n) A' R' a' ->
    Γ ▹ M ⊢< prop > q ≡ q' : acc (ty n) A R a ->
    Γ ▹ M ⊢< l > accel (ty n) l A R P p a q ≡ accel (ty n) l A' R' P' p' a' q' : P <[a ..]


| conv_obseq :
    ∀ Γ n A A' a a' b b',
    Γ ▹ M ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ▹ M ⊢< ty n > a ≡ a' : A ->
    Γ ▹ M ⊢< ty n > b ≡ b' : A ->
    Γ ▹ M ⊢< Ax prop > obseq (ty n) A a b ≡ obseq (ty n) A' a' b' : Sort prop

| conv_obsrefl :
  ∀ n Γ A A' a a',
    Γ ▹ M ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ▹ M ⊢< ty n > a ≡ a' : A ->
    Γ ▹ M ⊢< prop > obsrefl (ty n) A a ≡ obsrefl (ty n) A' a' : obseq (ty n) A a a

| conv_J :
    ∀ Γ n A A' a a' P P' p p' b b' e e',
      Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
      Γ ▹ M ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
      Γ ▹ M ⊢< ty n > a ≡ a' : A ->
      Γ ,, (ty n , A) ▹ M ⊢< Ax prop > P ≡ P' : Sort prop ->
      Γ ▹ M ⊢< prop > p ≡ p' : P <[a..] ->
      Γ ▹ M ⊢< ty n > b ≡ b' : A ->
      Γ ▹ M ⊢< prop > e ≡ e' : obseq (ty n) A a b ->
      Γ ▹ M ⊢< prop > J (ty n) A a P p b e ≡ J (ty n) A' a' P' p' b' e' : P <[b..]

| conv_cast :
  ∀ Γ i A A' B B' e e' a a',
    Γ ▹ M ⊢< Ax i > A ≡ A' : Sort i ->
    Γ ▹ M ⊢< Ax i > B ≡ B' : Sort i ->
    Γ ▹ M ⊢< prop > e : obseq (Ax i) (Sort i) A B ->
    Γ ▹ M ⊢< prop > e' : obseq (Ax i) (Sort i) A' B' ->
    Γ ▹ M ⊢< prop > e ≡ e' : obseq (Ax i) (Sort i) A B ->
    Γ ▹ M ⊢< i > a ≡ a' : A ->
    Γ ▹ M ⊢< i > cast i A B e a ≡ cast i A' B' e' a' : B

| conv_injpi1 :
  ∀ Γ i n A1 A1' A2 A2' B1 B1' B2 B2' e e',
    Γ ▹ M ⊢< Ax i > A1 : Sort i ->
    Γ ▹ M ⊢< Ax i > A1 ≡ A1' : Sort i ->
    Γ ,, (i, A1) ▹ M ⊢< Ax (ty n) > B1 ≡ B1' : Sort (ty n) ->
    Γ ▹ M ⊢< Ax i > A2 : Sort i ->
    Γ ▹ M ⊢< Ax i > A2 ≡ A2' : Sort i ->
    Γ ,, (i, A2) ▹ M ⊢< Ax (ty n) > B2 ≡ B2' : Sort (ty n) ->
    Γ ▹ M ⊢< prop > e ≡ e' : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ▹ M ⊢< prop > injpi1 i (ty n) A1 A2 B1 B2 e ≡ injpi1 i (ty n) A1' A2' B1' B2' e' : obseq (Ax i) (Sort i) A2 A1

| conv_injpi2 :
  ∀ Γ i n A1 A1' A2 A2' B1 B1' B2 B2' e e' a2 a2',
    Γ ▹ M ⊢< Ax i > A1 : Sort i ->
    Γ ▹ M ⊢< Ax i > A1 ≡ A1' : Sort i ->
    Γ ,, (i, A1) ▹ M ⊢< Ax (ty n) > B1 ≡ B1' : Sort (ty n) ->
    Γ ▹ M ⊢< Ax i > A2 : Sort i ->
    Γ ▹ M ⊢< Ax i > A2 ≡ A2' : Sort i ->
    Γ ,, (i, A2) ▹ M ⊢< Ax (ty n) > B2 ≡ B2' : Sort (ty n) ->
    Γ ▹ M ⊢< prop > e ≡ e' : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ▹ M ⊢< i > a2 ≡ a2' : A2 ->
    let a1 := cast i A2 A1 (injpi1 i (ty n) A1 A2 B1 B2 e) a2 in
    Γ ▹ M ⊢< prop > injpi2 i (ty n) A1 A2 B1 B2 e a2 ≡ injpi2 i (ty n) A1' A2' B1' B2' e' a2' : obseq (Ax (ty n)) (Sort (ty n)) (B1<[a1..]) (B2 <[a2..])

| conv_accelcomp :
    ∀ Γ n m A R a q P p A' R' a' q' P' p',
    Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop ->
    Γ ,, (ty n, A) ▹ M ⊢< Ax (ty m) > P : Sort (ty m) ->
    Γ ▹ M ⊢< Ax (ty n) > A ≡ A' : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R ≡ R' : Sort prop ->
    Γ ,, (ty n, A) ▹ M ⊢< Ax (ty m) > P ≡ P' : Sort (ty m) ->
    let R_ := (1 .: (0 .: (S >> S))) ⋅ R in
    let P_ := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi (ty n) (ty m) (S ⋅ A) (Pi prop (ty m) R_ P_) in
    let P'' := (1.: (S >> S)) ⋅ P in
    Γ ,, (ty n, A) ,, (Ru (ty n) (ty m), B) ▹ M ⊢< (ty m) > p ≡ p' : P'' ->
    Γ ▹ M ⊢< ty n > a ≡ a' : A ->
    Γ ▹ M ⊢< prop > q ≡ q' : acc (ty n) A R a ->
    let Awk := (S >> S) ⋅ A in
    let Rwk := (up_ren (up_ren (S >> S))) ⋅ R in
    let Pwk := (up_ren (S >> S)) ⋅ P in
    let pwk := (up_ren (up_ren (S >> S))) ⋅ p in
    let t0 := accinv (ty n) Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0) in
    let t1 := accel (ty n) (ty m) Awk Rwk Pwk pwk (var 1) t0 in
    let t2 := R<[S ⋅ a .: (var 0 .: S >> var)] in
    let t3 := lam prop (ty m) t2 P'' t1 in
    let t4 := Pi prop (ty m) t2 P'' in
    let t5 := lam (ty n) (ty m) A t4 t3 in
    Γ ▹ M ⊢< prop > accelcomp (ty n) (ty m) A R P p a q ≡ accelcomp (ty n) (ty m) A' R' P' p' a' q'
      : obseq (ty m) (P <[a ..]) (accel (ty n) (ty m) A R P p a q) (p <[ t5 .: a ..])


| conv_cast_refl :
    ∀ Γ i A e a,
      Γ ▹ M ⊢< prop > e : obseq (Ax i) (Sort i) A A ->
      Γ ▹ M ⊢< Ax i > A : Sort i ->
      Γ ▹ M ⊢< i > a : A ->
      Γ ▹ M ⊢< i > cast i A A e a ≡ a : A

| conv_cast_pi :
  ∀ Γ i n A1 A2 B1 B2 e f,
    Γ ▹ M ⊢< Ax i > A1 : Sort i ->
    Γ ,, (i, A1) ▹ M ⊢< Ax (ty n) > B1 : Sort (ty n) ->
    Γ ▹ M ⊢< Ax i > A2 : Sort i ->
    Γ ,, (i, A2) ▹ M ⊢< Ax (ty n) > B2 : Sort (ty n) ->
    Γ ▹ M ⊢< prop > e : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ▹ M ⊢< Ru i (ty n) > f : Pi i (ty n) A1 B1 ->
    let A1' := S ⋅ A1 in
    let A2' := S ⋅ A2 in
    let B1' := (up_ren S) ⋅ B1 in
    let B2' := (up_ren S) ⋅ B2 in
    let t1 := cast i A2' A1' (injpi1 i (ty n) A1' A2' B1' B2' (S ⋅ e)) (var 0) in
    let t2 := app i (ty n) A1' B1' (S ⋅ f) t1 in
    let t3 := cast (ty n) (B1 <[t1.: S >> var]) B2 (injpi2 i (ty n) A1' A2' B1' B2' (S ⋅ e) (var 0)) t2 in
    let t4 := lam i (ty n) A2 B2 t3 in
    Γ ▹ M ⊢< Ru i (ty n) > cast (Ru i (ty n)) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) e f ≡ t4 : Pi i (ty n) A2 B2


| conv_conv :
    ∀ Γ l A B t t',
      Γ ▹ M ⊢< l > t ≡ t' : A ->
      Γ ▹ M ⊢< Ax l > A ≡ B : Sort l ->
      Γ ▹ M ⊢< l > t ≡ t' : B

| conv_irrel :
    ∀ Γ A t t',
      Γ ▹ M ⊢< prop > t : A ->
      Γ ▹ M ⊢< prop > t' : A ->
      Γ ▹ M ⊢< prop > t ≡ t' : A

| conv_beta :
    ∀ Γ i j A B t u,
      Γ ▹ M ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ▹ M ⊢< Ax j > B : Sort j →
      Γ ,, (i , A) ▹ M ⊢< j > t : B →
      Γ ▹ M ⊢< i > u : A →
      Γ ▹ M ⊢< j > app i j A B (lam i j A B t) u ≡ t <[ u .. ] : B <[ u .. ]

| conv_eta :
    ∀ Γ i j A B t u,
      Γ ▹ M ⊢< Ax i > A : Sort i →
      Γ ,, (i , A) ▹ M ⊢< Ax j > B : Sort j →
      Γ ▹ M ⊢< Ru i j > t : Pi i j A B →
      Γ ▹ M ⊢< Ru i j > u : Pi i j A B →
      let t_app_x := app i j (S ⋅ A) ((up_ren S) ⋅ B) (S ⋅ t) (var 0) in
      let u_app_x := app i j (S ⋅ A) ((up_ren S) ⋅ B) (S ⋅ u) (var 0) in
      Γ ,, (i , A) ▹ M ⊢< j > t_app_x ≡ u_app_x : B →
      Γ ▹ M ⊢< Ru i j > t ≡ u : Pi i j A B

| conv_rec_zero :
    ∀ Γ l P p_zero p_succ,
      Γ ,, (ty 0 , Nat) ▹ M ⊢< Ax l > P : Sort l ->
      Γ ▹ M ⊢< l > p_zero : P <[ zero .. ] ->
      Γ ,, (ty 0 , Nat) ,, (l , P) ▹ M ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ->
      Γ ▹ M ⊢< l > rec l P p_zero p_succ zero ≡ p_zero : P <[ zero .. ]

| conv_rec_succ :
    ∀ Γ l P p_zero p_succ t,
      Γ ,, (ty 0 , Nat) ▹ M ⊢< Ax l > P : Sort l ->
      Γ ▹ M ⊢< l > p_zero : P <[ zero .. ] ->
      Γ ,, (ty 0 , Nat) ,, (l , P) ▹ M ⊢< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]  ->
      Γ ▹ M ⊢< ty 0 > t : Nat ->
      Γ ▹ M ⊢< l > rec l P p_zero p_succ (succ t) ≡
          p_succ <[(rec l P p_zero p_succ t) .: t ..] : P <[ (succ t) .. ]

| conv_accel_accin :
    ∀ Γ n m A R a q P p,
    M = mdef ->
    Γ ▹ M ⊢< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ▹ M ⊢< Ax prop > R : Sort prop ->
    Γ ,, (ty n, A) ▹ M ⊢< Ax (ty m) > P : Sort (ty m) ->
    let R' := (1 .: (0 .: (S >> S))) ⋅ R in
    let P' := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi (ty n) (ty m) (S ⋅ A) (Pi prop (ty m) R' P') in
    let P'' := (1.: (S >> S)) ⋅ P in
    Γ ,, (ty n, A) ,, (Ru (ty n) (ty m), B) ▹ M ⊢< ty m > p : P'' ->
    Γ ▹ M ⊢< ty n > a : A ->
    Γ ▹ M ⊢< prop > q : acc (ty n) A R a ->
    let Awk := (S >> S) ⋅ A in
    let Rwk := (up_ren (up_ren (S >> S))) ⋅ R in
    let Pwk := (up_ren (S >> S)) ⋅ P in
    let pwk := (up_ren (up_ren (S >> S))) ⋅ p in
    let t0 := accinv (ty n) Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0) in
    let t1 := accel (ty n) (ty m) Awk Rwk Pwk pwk (var 1) t0 in
    let t2 := R<[S ⋅ a .: (var 0 .: S >> var)] in
    let t3 := lam prop (ty m) t2 P'' t1 in
    let t4 := Pi prop (ty m) t2 P'' in
    let t5 := lam (ty n) (ty m) A t4 t3 in
    Γ ▹ M ⊢< ty m > accel (ty n) (ty m) A R P p a q ≡ p <[ t5 .: a ..] : P <[a ..]

| conv_sym :
    ∀ Γ l t u A,
      Γ ▹ M ⊢< l > t ≡ u : A ->
      Γ ▹ M ⊢< l > u ≡ t : A

| conv_trans :
    ∀ Γ l t u v A,
      Γ ▹ M ⊢< l > t ≡ u : A ->
      Γ ▹ M ⊢< l > u ≡ v : A ->
      Γ ▹ M ⊢< l > t ≡ v : A

where "Γ ▹ M ⊢< l > t : A" := (typing M Γ l t A)
and   "▹ M ⊢ Γ" := (ctx_typing M Γ)
and   "Γ ▹ M ⊢< l > t ≡ u : A" := (conversion M Γ l t u A).

Scheme typing_mut := Induction for typing Sort Prop
with conversion_mut := Induction for conversion Sort Prop.

Combined Scheme typing_mutind from typing_mut, conversion_mut.

Scheme type_mut := Induction for typing Sort Prop
with conv_mut := Induction for conversion Sort Prop
with ctx_mut := Induction for ctx_typing Sort Prop.

Combined Scheme type_conv_ctx_mut from type_mut, conv_mut, ctx_mut.

Parameter assm_sig_ty :
  ∀ c A,
    nth_error assm_sig c = Some A ->
    ∙ ▹ mprop ⊢< Ax prop > A : Sort prop <-> ∙ ▹ mdef ⊢< Ax prop > A : Sort prop.

Reserved Notation "Γ ⊢r ρ : Δ" (at level 50, ρ, Δ at next level).

Inductive WellRen (Γ : ctx) (ρ : nat → nat) : ctx → Prop :=
| well_rempty : Γ ⊢r ρ : ∙
| well_rcons Δ l A :
  Γ ⊢r (↑ >> ρ) : Δ →
  Γ ∋< l > ρ 0 : (S >> ρ) ⋅ A →
  Γ ⊢r ρ : Δ ,, (l , A)
where "Γ ⊢r ρ : Δ" := (WellRen Γ ρ Δ).

Reserved Notation "Γ ▹ M ⊢s σ : Δ" (at level 50, M, σ, Δ at next level).

Reserved Notation "Γ ▹ M ⊢s σ ≡ τ : Δ" (at level 50, M, σ, τ, Δ at next level).

Inductive WellSubst (Γ : ctx) (M : mode) : ctx -> (nat -> term) -> Prop :=
| well_sempty (σ : nat -> term) :
  Γ ▹ M ⊢s σ : ∙
| well_scons (σ : nat -> term) (Δ : ctx) l (A : term) :
  Γ ▹ M ⊢s (↑ >> σ) : Δ ->
  Γ ▹ M ⊢< l > σ 0 : A <[↑ >> σ] ->
  Γ ▹ M ⊢s σ : (Δ ,, (l , A))
where "Γ ▹ M ⊢s σ : Δ" := (WellSubst Γ M Δ σ).

Inductive ConvSubst (Γ : ctx) M : ctx -> (nat -> term) -> (nat -> term) -> Prop :=
| conv_sempty (σ τ : nat -> term) : Γ ▹ M ⊢s σ ≡ τ : ∙
| conv_scons (σ τ : nat -> term) (Δ : ctx) l A :
  Γ ▹ M ⊢s (↑ >> σ) ≡ (↑ >> τ) : Δ ->
  Γ ▹ M ⊢< l > σ var_zero ≡ τ var_zero: A <[↑ >> σ] ->
  Γ ▹ M ⊢s σ ≡ τ : Δ ,, (l , A)
where "Γ ▹ M ⊢s σ ≡ τ : Δ" := (ConvSubst Γ M Δ σ τ).

Reserved Notation "▹ M ⊢ Γ ≡ Δ" (at level 50, Δ at next level).

Inductive ConvCtx M :ctx -> ctx -> Prop :=
| conv_cempty : ▹ M ⊢ ∙ ≡ ∙
| conv_ccons Γ A Δ B l :
  ▹ M ⊢ Γ ≡ Δ ->
  Γ ▹ M ⊢< Ax l > A ≡ B : Sort l ->
  ▹ M ⊢ (Γ ,, ( l , A)) ≡ (Δ ,, (l , B))
where "▹ M ⊢ Γ ≡ Δ" := (ConvCtx M Γ Δ).

Notation "Γ ⊢d< l > t : T" :=
  (typing mdef Γ l t T)
  (at level 50, l, t, T at next level).

Notation "Γ ⊢d< l > t ≡ u : T" :=
  (conversion mdef Γ l t u T)
  (at level 50, l, t, u, T at next level).

Notation "⊢d Γ" :=
  (ctx_typing mdef Γ)
  (at level 50, Γ at next level).

Notation "Γ ⊢ds σ : Δ" :=
  (WellSubst Γ mdef Δ σ)
  (at level 50, σ, Δ at next level).

Notation "Γ ⊢ds σ ≡ τ : Δ" :=
  (ConvSubst Γ mdef Δ σ τ)
  (at level 50, σ, τ, Δ at next level).

Notation "⊢d Γ ≡ Δ" :=
  (ConvCtx mdef Γ Δ)
  (at level 50, Γ, Δ at next level).

Notation "Γ ⊢p< l > t : T" :=
  (typing mprop Γ l t T)
  (at level 50, l, t, T at next level).

Notation "Γ ⊢p< l > t ≡ u : T" :=
  (conversion mprop Γ l t u T)
  (at level 50, l, t, u, T at next level).

Notation "⊢p Γ" :=
  (ctx_typing mprop Γ)
  (at level 50, Γ at next level).

Notation "Γ ⊢ps σ : Δ" :=
  (WellSubst Γ mprop Δ σ)
  (at level 50, σ, Δ at next level).

Notation "Γ ⊢ps σ ≡ τ : Δ" :=
  (ConvSubst Γ mprop Δ σ τ)
  (at level 50, σ, τ, Δ at next level).

Notation "⊢p Γ ≡ Δ" :=
  (ConvCtx mprop Γ Δ)
  (at level 50, Γ, Δ at next level).

Fixpoint scoped n t :=
  match t with
  | var m => m <? n
  | Sort _ => true
  | assm c => true
  | Pi i j A B => scoped n A && scoped (S n) B
  | lam i j A B t => scoped n A && scoped (S n) B && scoped (S n) t
  | app i j A B u v => scoped n A && scoped (S n) B && scoped n u && scoped n v
  | Nat => true
  | zero => true
  | succ k => scoped n k
  | rec _ P pz ps t =>
    scoped (S n) P && scoped n pz && scoped (S (S n)) ps && scoped n t
  | acc _ A R a => scoped n A && scoped (S (S n)) R && scoped n a
  | accin i A R a p  =>
    scoped n A && scoped (S (S n)) R && scoped n a && scoped n p
  | accinv i A R a p b r =>
    scoped n A && scoped (S (S n)) R && scoped n a && scoped n p &&
    scoped n b && scoped n r
  | accel _ _ A R a q P p =>
    scoped n A && scoped (S (S n)) R && scoped (S n) a && scoped (S ( S n)) q &&
    scoped n P && scoped n p
  | accelcomp _ _ A R a q P p =>
    scoped n A && scoped (S (S n)) R && scoped (S n) a && scoped (S ( S n)) q &&
    scoped n P && scoped n p
  | obseq _ A a b => scoped n A && scoped n a && scoped n b
  | obsrefl l A a => scoped n A && scoped n a
  | J l A a P p b e =>
    scoped n A && scoped n a && scoped (S n) P && scoped n p && scoped n b &&
    scoped n e
  | cast _ A B e t => scoped n A && scoped n B && scoped n e && scoped n t
  | injpi1 i j A1 A2 B1 B2 e =>
    scoped n A1 && scoped n A2 && scoped (S n) B1 && scoped (S n) B2 &&
    scoped n e
  | injpi2 i j A1 A2 B1 B2 e a2 =>
    scoped n A1 && scoped n A2 && scoped (S n) B1 && scoped (S n) B2 &&
    scoped n e && scoped n a2
  end.

Notation closed t := (scoped 0 t).
