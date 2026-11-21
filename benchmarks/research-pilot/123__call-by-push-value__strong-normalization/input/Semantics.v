Set Implicit Arguments.

Require Import Logic List Classes.Morphisms.

Import List Notations.

Require Export CBPV.Terms CBPV.Base CBPV.AbstractReductionSystems.

Import CommaNotation.

Reserved Notation "A '≽' B" (at level 80).

Reserved Notation "A '⇝' B" (at level 80).

Inductive pstep {n: nat}: comp n -> comp n -> Prop :=
| pstepForce (c: comp n):
    <{c}>! ≽ c
| pstepApp (c: comp (S n)) (c': comp n) v:
    c[v..] = c' -> (lambda c) v ≽ c'
| pstepProj (b: bool) (c c1 c2: comp n) :
    (c = if b then c1 else c2) -> proj b (tuple c1 c2) ≽ c
| pstepLetin (c: comp (S n)) c' v:
    c[v..] = c' -> $ <- (ret v); c ≽ c'
| pstepCaseS v (b: bool) c (c1 c2: comp (S n)):
    (if b then c1 else c2)[v..] = c -> caseS (inj b v) c1 c2 ≽ c
| pstepCaseP v1 v2 (c: comp (S (S n))) c':
    c[v2,v1..] = c' -> caseP (pair v1 v2) c ≽ c'
where "A '≽' B" := (pstep A B).

Inductive step {n: nat}: comp n -> comp n -> Prop :=
| stepPrimitive (c c': comp n) : c ≽ c' -> c > c'
| stepApp (c c': comp n) v: c > c' -> c v > c' v
| stepProj (c c': comp n)  b: c > c' -> proj b c > proj b c'
| stepLetin (c1 c1': comp n) c2: c1 > c1' -> $ <- c1; c2 > $ <- c1'; c2
where "A > B" := (step A B).

Notation "A >* B" := (star step A B) (at level 60).

Notation "A >+ B" := (plus step A B) (at level 60).

Inductive ectx {n: nat}: Type :=
| ectxHole : ectx
| ectxApp : ectx -> value n -> ectx
| ectxProj : bool -> ectx -> ectx
| ectxLetin : ectx -> comp (S n) -> ectx.

Fixpoint fill {n: nat} (K: ectx) (c: comp n) :=
  match K with
  | ectxHole => c
  | ectxApp K v => (fill K c) v
  | ectxProj b K => proj b (fill K c)
  | ectxLetin K c' => letin (fill K c) c'
  end.

Inductive cstep {n: nat}: comp n -> comp n -> Prop :=
| contextStep C c c' (c'' c''': comp n):
    c ≽ c' -> fill C c = c'' -> fill C c' = c''' -> c'' ⇝ c'''
where "A '⇝' B" := (cstep A B).

Reserved Notation "A ▷ B" (at level 80).

Inductive bigstep {n: nat}: comp n -> comp n -> Prop :=
| bigstepCu: @cu n ▷ cu
| bigstepReturn (v: value n) : ret v ▷ ret v
| bigstepLambda (c: comp (S n)) : lambda c ▷ lambda c
| bigstepTuple (c1 c2: comp n): tuple c1 c2 ▷ tuple c1 c2
| bigstepForce (c c': comp n): c ▷ c' -> <{c}>! ▷ c'
| bigstepApp (c c'': comp n) c' v: c ▷ lambda c' -> c'[v..] ▷ c'' -> c v ▷ c''
| bigstepProj c c' (c1 c2: comp n) (b: bool):
    c ▷ tuple c1 c2 -> (if b then c1 else c2) ▷ c' -> proj b c ▷ c'
| bigstepLetin c1 (v: value n) c2 c: c1 ▷ ret v -> c2[v..] ▷ c -> $ <- c1; c2 ▷ c
| bigstepCaseS c c1 c2 (b: bool) (v: value n):
    (if b then c1 else c2)[v..] ▷ c -> caseS (inj b v) c1 c2 ▷ c
| bigstepCaseP c c' (v1 v2: value n):
    c[v2,v1..] ▷ c' -> caseP (pair v1 v2) c ▷ c'
where "A ▷ B" := (bigstep A B).

Inductive nf {n: nat}: comp n -> Prop :=
| nfCu: nf cu
| nfLam c: nf (lambda c)
| nfTup c1 c2: nf (tuple c1 c2)
| nfRet v: nf (ret v).

Definition eval {n: nat} (c c': comp n) := c >* c' /\ nf c'.
