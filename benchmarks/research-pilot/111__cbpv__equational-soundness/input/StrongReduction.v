Set Implicit Arguments.

Require Import Logic List Classes.Morphisms.

Import List Notations.

Require Export CBPV.ProgramContexts CBPV.Semantics.

Import CommaNotation.

Reserved Notation "C1 ⇒ C2" (at level 60).

Reserved Notation "V1 ⇒ᵥ V2" (at level 60).

Inductive strong_step {n: nat} : comp n -> comp n -> Prop :=
| strong_reduce  m (c1 c2: comp m) (K: cctx false n m):
    c1 ≽ c2 -> fillc K c1 ⇒ fillc K c2
where "C1 ⇒ C2" := (strong_step C1 C2).

Inductive strong_step_value {n : nat} : value n -> value n -> Prop :=
| strong_reduce_value k (c1 c2 : comp k) (K : vctx false n k) :
    c1 ≽ c2 -> fillv K c1 ⇒ᵥ fillv K c2
where "V1 ⇒ᵥ V2" := (strong_step_value V1 V2).

Reserved Notation "C1 ↪ C2" (at level 60).

Reserved Notation "V1 ↪ᵥ V2" (at level 60).

Inductive sstep {n: nat} : comp n -> comp n -> Prop :=
| sstepForce (v v': value n): v ↪ᵥ v' -> v ! ↪ v' !
| sstepLambda (c c': comp (S n)): c ↪ c' -> lambda c ↪ lambda c'
| sstepAppL (c c': comp n) v: c ↪ c' -> c v ↪ c' v
| sstepAppR (c: comp n) (v v': value n): v ↪ᵥ v' -> c v ↪ c v'
| sstepTupleL (c1 c1': comp n) c2: c1 ↪ c1' -> tuple c1 c2 ↪ tuple c1' c2
| sstepTupleR c1 (c2 c2': comp n): c2 ↪ c2' -> tuple c1 c2 ↪ tuple c1 c2'
| sstepRet (v v': value n): v ↪ᵥ v' -> ret v ↪ ret v'
| sstepLetinL (c1 c1': comp n) c2: c1 ↪ c1' -> letin c1 c2 ↪ letin c1' c2
| sstepLetinR c1 (c2 c2': comp (S n)): c2 ↪ c2' -> letin c1 c2 ↪ letin c1 c2'
| sstepProj (c c': comp n) b: c ↪ c' -> proj b c ↪ proj b c'
| sstepCaseZ (v v': value n): v ↪ᵥ v' -> caseZ v ↪ caseZ v'
| sstepCaseSV (v v': value n) c1 c2: v ↪ᵥ v' -> caseS v c1 c2 ↪ caseS v' c1 c2
| sstepCaseSL (v: value n) c1 c1' c2: c1 ↪ c1' -> caseS v c1 c2 ↪ caseS v c1' c2
| sstepCaseSR (v: value n) c1 c2 c2': c2 ↪ c2' -> caseS v c1 c2 ↪ caseS v c1 c2'
| sstepCasePV (v v': value n) c: v ↪ᵥ v' -> caseP v c ↪ caseP v' c
| sstepCasePC (v: value n) c c': c ↪ c' -> caseP v c ↪ caseP v c'
| sstepPrimitive (c c': comp n) : c ≽ c' -> c ↪ c'
where "C1 ↪ C2" := (@sstep _ C1 C2)
with sstep_value {n: nat} : value n -> value n -> Prop :=
| sstepValuePairL (v1 v1' v2: value n) : v1 ↪ᵥ v1' -> pair v1 v2 ↪ᵥ pair v1' v2
| sstepValuePairR (v1 v2 v2': value n) : v2 ↪ᵥ v2' -> pair v1 v2 ↪ᵥ pair v1 v2'
| sstepValueInj b (v v': value n) : v ↪ᵥ v' -> inj b v ↪ᵥ inj b v'
| sstepValueThunk (c c': comp n) : c ↪ c' -> <{ c }> ↪ᵥ <{ c' }>
where "V1 ↪ᵥ V2" := (@sstep_value _ V1 V2).

Scheme sstep_value_ind_2 := Induction for sstep_value Sort Prop
  with sstep_ind_2  := Induction for sstep Sort Prop.

Combined Scheme mutind_sstep from sstep_ind_2, sstep_value_ind_2.

Notation "M ↪* N" := (star sstep M N) (at level 60).

Notation "M ↪ᵥ* N" := (star sstep_value M N) (at level 60).
