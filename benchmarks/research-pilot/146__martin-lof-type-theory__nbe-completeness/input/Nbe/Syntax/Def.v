Set Implicit Arguments.

Require Import List.

Inductive Tm : Set :=
| TmVar    : Tm
| TmApp    : Tm -> Tm -> Tm
| TmAbs    : Tm -> Tm -> Tm
| Tm0      : Tm
| TmS      : Tm -> Tm
| TmSb     : Tm -> Sb -> Tm
| Tm1      : Tm
| TmNat    : Tm
| TmUnit   : Tm
| TmFun    : Tm -> Tm -> Tm
| TmEmpty  : Tm
| TmAbsurd : Tm -> Tm
| TmUniv   : Tm




with Sb : Set :=
| Sid  : Sb
| Sup  : Sb
| Sseq : Sb -> Sb -> Sb
| Sext : Sb -> Tm -> Sb
.

Definition Ssing t := (Sext Sid t).

Fixpoint tmVar (i:nat) :=
  match i with
    | 0   => TmVar
    | S k => TmSb (tmVar k) Sup
  end
.

Fixpoint Sups (i:nat) :=
  match i with
    | 0   => Sid
    | S k => Sseq (Sups k) Sup
  end
.

Definition TmArr A B := TmFun A (TmSb B Sup).

Definition Cxt := list Tm.

Definition Cext (G:Cxt) t := (t::G).

Notation "G ,, t" := (t::G)
 (left associativity, at level 73, t at next level).
