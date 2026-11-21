From Stdlib Require Import Utf8 List Arith Bool Lia Wellfounded.Inverse_Image Wellfounded.Inclusion.

From AccInSProp Require Import core unscoped AST SubstNotations Util BasicAST Typing.

From Stdlib Require Import Setoid Morphisms Relation_Definitions.

Import CombineNotations.

Reserved Notation "Γ ⊢d< l > t --> u : T" (at level 50, l, t, u, T at next level).

Definition val t :=
    match t with
    | app i j A B t u => False
    | rec i P pzero psucc n => False
    | accel _ _ A R a q P p => False
    | cast _ _ _ _ _ => False
    | _ => True
    end.

Inductive red  : ctx -> level -> term -> term -> term -> Prop :=
| red_app Γ t t' u i j A B :
    Γ ⊢d< Ax i > A : Sort i ->
    Γ ,, (i, A) ⊢d< Ax j > B : Sort j ->
    Γ ⊢d< Ru i j > t --> t' : Pi i j A B ->
    Γ ⊢d< i > u : A ->
    Γ ⊢d< j > app i j A B t u --> app i j A B t' u : B <[ u..]

| red_beta Γ t u i j A B A' B' :
    Γ ⊢d< Ax i > A ≡ A' : Sort i ->
    Γ ,, (i, A) ⊢d< Ax j > B ≡ B' : Sort j ->
      Γ ,, (i , A) ⊢d< j > t : B →
      Γ ⊢d< i > u : A →
    Γ ⊢d< j > app i j A B (lam i j A' B' t) u --> t <[ u.. ] : B <[ u..]

| red_rec Γ l P p_zero p_succ n n' :
    Γ ,, (ty 0 , Nat) ⊢d< Ax l > P : Sort l ->
    Γ ⊢d< l > p_zero : P <[ zero .. ] ->
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢d< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
    Γ ⊢d< ty 0 > n --> n' : Nat ->
    Γ ⊢d< l > rec l P p_zero p_succ n --> rec l P p_zero p_succ n' : P <[ n.. ]

| red_rec_zero Γ l P p_zero p_succ :
    Γ ,, (ty 0 , Nat) ⊢d< Ax l > P : Sort l ->
    Γ ⊢d< l > p_zero : P <[ zero .. ] ->
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢d< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
    Γ ⊢d< l > rec l P p_zero p_succ zero --> p_zero : P <[ zero .. ]

| red_rec_succ Γ l P p_zero p_succ n :
    Γ ,, (ty 0 , Nat) ⊢d< Ax l > P : Sort l ->
    Γ ⊢d< l > p_zero : P <[ zero .. ] ->
    Γ ,, (ty 0 , Nat) ,, (l , P) ⊢d< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] ->
    Γ ⊢d< ty 0 > n : Nat ->
    Γ ⊢d< l > rec l P p_zero p_succ (succ n) --> p_succ <[  (rec l P p_zero p_succ n) .: n ..] : P <[ (succ n) .. ]

| red_accel Γ n l A R a q P p :
    Γ ⊢d< Ax (ty n) > A : Sort (ty n) ->
    Γ ,, (ty n, A) ,, (ty n, S ⋅ A) ⊢d< Ax prop > R : Sort prop ->
    Γ ,, (ty n, A) ⊢d< Ax l > P : Sort l ->
    let R' := (1 .: (0 .: (S >> S))) ⋅ R in
    let P' := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi (ty n) l (S ⋅ A) (Pi prop l R' P') in
    let P'' := (1.: (S >> S)) ⋅ P in
    Γ ,, (ty n, A) ,, (Ru (ty n) l, B) ⊢d< l > p : P'' ->
    Γ ⊢d< ty n > a : A ->
    Γ ⊢d< prop > q : acc (ty n) A R a ->
    let Awk := (S >> S) ⋅ A in
    let Rwk := (up_ren (up_ren (S >> S))) ⋅ R in
    let Pwk := (up_ren (S >> S)) ⋅ P in
    let pwk := (up_ren (up_ren (S >> S))) ⋅ p in
    let t0 := accinv (ty n) Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0) in
    let t1 := accel (ty n) l Awk Rwk Pwk pwk (var 1) t0 in
    let t2 := R<[S ⋅ a .: (var 0 .: S >> var)] in
    let t3 := lam prop l t2 P'' t1 in
    let t4 := Pi prop l t2 P'' in
    let t5 := lam (ty n) l A t4 t3 in
    Γ ⊢d< l > accel (ty n) l A R P p a q --> p <[ t5 .: a ..] : P <[a ..]

| red_conv Γ l t u A B :
    Γ ⊢d< l > t --> u : A ->
    Γ ⊢d< Ax l > A ≡ B : Sort l ->
    Γ ⊢d< l > t --> u : B

| red_cast1 Γ i A A' B e a :
    Γ ⊢d< Ax i > A --> A' : Sort i ->
    Γ ⊢d< Ax i > B : Sort i ->
    Γ ⊢d< prop > e : obseq (Ax i) (Sort i) A B ->
    Γ ⊢d< i > a : A ->
    Γ ⊢d< i > cast i A B e a --> cast i A' B e a : B

| red_cast2 Γ i A B B' e a :
    Γ ⊢d< Ax i > A : Sort i ->
    val A ->
    Γ ⊢d< Ax i > B --> B' : Sort i ->
    Γ ⊢d< prop > e : obseq (Ax i) (Sort i) A B ->
    Γ ⊢d< i > a : A ->
    Γ ⊢d< i > cast i A B e a --> cast i A B' e a : B

| red_cast_nat Γ e t :
    Γ ⊢d< prop > e : obseq (ty 1) (Sort (ty 0)) Nat Nat ->
    Γ ⊢d< ty 0 > t : Nat ->
    Γ ⊢d< ty 0 > cast (ty 0) Nat Nat e t --> t : Nat

| red_cast_sort Γ i A e :
    Γ ⊢d< Ax i > A : Sort i ->
    Γ ⊢d< prop > e : obseq (Ax (Ax i)) (Sort (Ax i)) (Sort i) (Sort i) ->
    Γ ⊢d< Ax i > cast (Ax i) (Sort i) (Sort i) e A --> A : Sort i

| red_cast_pi Γ i n A1 A2 B1 B2 e f :
    Γ ⊢d< Ax i > A1 : Sort i ->
    Γ ,, (i, A1) ⊢d< Ax (ty n) > B1 : Sort (ty n) ->
    Γ ⊢d< Ax i > A2 : Sort i ->
    Γ ,, (i, A2) ⊢d< Ax (ty n) > B2 : Sort (ty n) ->
    Γ ⊢d< prop > e : obseq (Ax (Ru i (ty n))) (Sort (Ru i (ty n))) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) ->
    Γ ⊢d< Ru i (ty n) > f : Pi i (ty n) A1 B1 ->
    let A1' := S ⋅ A1 in
    let A2' := S ⋅ A2 in
    let B1' := (up_ren S) ⋅ B1 in
    let B2' := (up_ren S) ⋅ B2 in
    let t1 := cast i A2' A1' (injpi1 i (ty n) A1' A2' B1' B2' (S ⋅ e)) (var 0) in
    let t2 := app i (ty n) A1' B1' (S ⋅ f) t1 in
    let t3 := cast (ty n) (B1 <[t1.: S >> var]) B2 (injpi2 i (ty n) A1' A2' B1' B2' (S ⋅ e) (var 0)) t2 in
    let t4 := lam i (ty n) A2 B2 t3 in
    Γ ⊢d< Ru i (ty n) > cast (Ru i (ty n)) (Pi i (ty n) A1 B1) (Pi i (ty n) A2 B2) e f --> t4 : Pi i (ty n) A2 B2

where "Γ ⊢d< l > t --> u : T" := (red Γ l t u T).

Reserved Notation "Γ ⊢d< l > t -->> u : T" (at level 50, l, t, u, T at next level).

Inductive redd : ctx -> level -> term -> term -> term -> Prop :=
  | redd_refl Γ l t A : Γ ⊢d< l > t : A -> Γ ⊢d< l > t -->> t : A
  | redd_step Γ l t u v A : Γ ⊢d< l > t --> v : A -> Γ ⊢d< l > v -->> u : A -> Γ ⊢d< l > t -->>u : A
where "Γ ⊢d< l > t -->> t' : A " := (redd Γ l t t' A).

Definition whnf Γ l t A := forall u, Γ ⊢d< l > t --> u : A -> False.

Definition redd_whnf Γ l t t' A := redd Γ l t t' A /\ whnf Γ l t' A.

Notation "Γ ⊢d< l > t -->>! u : T" := (redd_whnf Γ l t u T) (at level 50, l, t, u, T at next level).

Definition red_inv_type Γ t v :=
    match t with
    | app i j A B (lam i' j' A' B' t) u =>
        i = i' /\
        j = j' /\
        v = t <[ u.. ] /\
        Γ ⊢d< Ax i > A ≡ A' : Sort i /\
        Γ ,, (i , A) ⊢d< Ax j > B ≡ B' : Sort j /\
        Γ ,, (i , A) ⊢d< j > t : B /\
        Γ ⊢d< i > u : A
    | app i j A B t u =>
        exists t',
            v = app i j A B t' u /\
            Γ ⊢d< Ax i > A : Sort i /\
            Γ ,, (i, A) ⊢d< Ax j > B : Sort j /\
            Γ ⊢d< Ru i j > t --> t' : Pi i j A B /\
            Γ ⊢d< i > u : A
    | rec l P p_zero p_succ zero =>
        v = p_zero /\
        Γ ,, (ty 0 , Nat) ⊢d< Ax l > P : Sort l /\
        Γ ⊢d< l > p_zero : P <[ zero .. ] /\
        Γ ,, (ty 0 , Nat) ,, (l , P) ⊢d< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ]
    | rec l P p_zero p_succ (succ n) =>
        v = p_succ <[  (rec l P p_zero p_succ n) .: n ..] /\
        Γ ,, (ty 0 , Nat) ⊢d< Ax l > P : Sort l /\
        Γ ⊢d< l > p_zero : P <[ zero .. ] /\
        Γ ,, (ty 0 , Nat) ,, (l , P) ⊢d< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] /\
        Γ ⊢d< ty 0 > n : Nat
    | rec l P p_zero p_succ n =>
        exists n',
            v = rec l P p_zero p_succ n' /\
            Γ ,, (ty 0 , Nat) ⊢d< Ax l > P : Sort l /\
            Γ ⊢d< l > p_zero : P <[ zero .. ] /\
            Γ ,, (ty 0 , Nat) ,, (l , P) ⊢d< l > p_succ : P <[ (succ (var 1)) .: (shift >> (shift >> var)) ] /\
            Γ ⊢d< ty 0 > n --> n' : Nat
    | accel i l A R P p a q =>
    let R' := (1 .: (0 .: (S >> S))) ⋅ R in
    let P' := (1 .: (S >> S >> S)) ⋅ P in
    let B := Pi i l (S ⋅ A) (Pi prop l R' P') in
    let P'' := (1.: (S >> S)) ⋅ P in
    let Awk := (S >> S) ⋅ A in
    let Rwk := (up_ren (up_ren (S >> S))) ⋅ R in
    let Pwk := (up_ren (S >> S)) ⋅ P in
    let pwk := (up_ren (up_ren (S >> S))) ⋅ p in
    let t0 := accinv i Awk Rwk ((S >> S) ⋅ a) ((S >> S) ⋅ q) (var 1) (var 0) in
    let t1 := accel i l Awk Rwk Pwk pwk (var 1) t0 in
    let t2 := R<[S ⋅ a .: (var 0 .: S >> var)] in
    let t3 := lam prop l t2 P'' t1 in
    let t4 := Pi prop l t2 P'' in
    let t5 := lam i l A t4 t3 in
        v = p <[ t5 .: a ..] /\
        Γ ⊢d< Ax i > A : Sort i /\
        Γ ,, (i, A) ,, (i, S ⋅ A) ⊢d< Ax prop > R : Sort prop /\
        Γ ,, (i, A) ⊢d< Ax l > P : Sort l /\
        Γ ,, (i, A) ,, (Ru i l, B) ⊢d< l > p : P'' /\
        Γ ⊢d< i > a : A /\
        Γ ⊢d< prop > q : acc i A R a /\
        exists n, i = ty n
    | cast _ Nat Nat e t =>
        v = t /\
        Γ ⊢d< prop > e : obseq (ty 1) (Sort (ty 0)) Nat Nat /\
        Γ ⊢d< ty 0 > t : Nat
    | cast l (Sort i) (Sort j) e A =>
        v = A /\
        Γ ⊢d< Ax i > A : Sort i /\
        Γ ⊢d< prop > e : obseq (Ax (Ax i)) (Sort (Ax i)) (Sort i) (Sort i) /\
        i = j /\
        l = Ax i
    | cast l (Pi i j A1 B1) (Pi i' j' A2 B2) e f =>
        let A1' := S ⋅ A1 in
        let A2' := S ⋅ A2 in
        let B1' := (up_ren S) ⋅ B1 in
        let B2' := (up_ren S) ⋅ B2 in
        let t1 := cast i A2' A1' (injpi1 i j A1' A2' B1' B2' (S ⋅ e)) (var 0) in
        let t2 := app i j A1' B1' (S ⋅ f) t1 in
        let t3 := cast j (B1 <[t1.: S >> var]) B2 (injpi2 i j A1' A2' B1' B2' (S ⋅ e) (var 0)) t2 in
        let t4 := lam i j A2 B2 t3 in
        v = t4 /\
        Γ ⊢d< Ax i > A1 : Sort i /\
        Γ ,, (i, A1) ⊢d< Ax j > B1 : Sort j /\
        Γ ⊢d< Ax i > A2 : Sort i /\
        Γ ,, (i, A2) ⊢d< Ax j > B2 : Sort j /\
        Γ ⊢d< prop > e : obseq (Ax (Ru i j)) (Sort (Ru i j)) (Pi i j A1 B1) (Pi i j A2 B2) /\
        Γ ⊢d< Ru i j > f : Pi i j A1 B1 /\
        l = Ru i j /\
        i' = i /\
        exists n,
        j = ty n /\
        j' = ty n

    | cast i A B e t =>
        (exists A',
            v = cast i A' B e t /\
            Γ ⊢d< Ax i > A --> A' : Sort i /\
            Γ ⊢d< Ax i > B : Sort i /\
            Γ ⊢d< prop > e : obseq (Ax i) (Sort i) A B /\
            Γ ⊢d< i > t : A) \/
        (exists B',
            v = cast i A B' e t /\
            val A /\
            Γ ⊢d< Ax i > B --> B' : Sort i /\
            Γ ⊢d< Ax i > A : Sort i /\
            Γ ⊢d< prop > e : obseq (Ax i) (Sort i) A B /\
            Γ ⊢d< i > t : A)
    | _ => False
    end.

Fixpoint size (t : term) : nat :=
  match t with
  | var _ => 0
  | Sort _ => 0
  | Pi _ _ A B => 1 + size A + size B
  | lam _ _ A B t => 1 + size A + size B + size t
  | app _ _ A B t u => 1 + size A + size B + size t + size u
  | Nat => 0
  | zero => 0
  | succ t => 1 + size t
  | rec _ P p0 ps t => 1 + size P + size p0 + size ps + size t
  | accel _ _ A R a q P p => 1 + size A + size R + size a + size q + size P + size p
  | acc _ A R a => 1 + size A + size R + size a
  | cast _ A B e t => 1 + size A + size B + size e + size t
  | obseq _ A a b => 1 + size A + size a + size b
  | _ => 0
end.

Reserved Notation "Γ ⊢d< l > t ~ u : T" (at level 50, l, t, u, T at next level).

Inductive ann_conv : ctx -> level -> term -> term -> term -> Prop :=

| aconv_refl :
    ∀ Γ l t A,
      Γ ⊢d< l > t : A ->
      Γ ⊢d< l > t ~ t : A

| aconv_app :
    ∀ Γ i j A B t u A' B' t' T,
      Γ ⊢d< Ax i > A ≡ A' : Sort i →
      Γ ,, (i , A) ⊢d< Ax j > B ≡ B': Sort j →
      Γ ⊢d< Ru i j > t ~ t' : Pi i j A B →
      Γ ⊢d< i > u : A →
      Γ ⊢d< Ax j > T ≡ B <[ u.. ] : Sort j ->
      Γ ⊢d< j > app i j A B t u ~ app i j A' B' t' u : T

where "Γ ⊢d< l > t ~ u : A" := (ann_conv Γ l t u A).
