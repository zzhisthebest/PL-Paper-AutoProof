Require Export cbpv.autosubst2.fintype.

From Coq Require Import FunctionalExtensionality.

Structure POSR : Type := mkPOSR {

  A : Set;


  zero : A;
  one : A;
  add : A -> A -> A;
  mult : A -> A -> A;


  add_lident : forall (a : A), add zero a = a;
  add_rident : forall (a : A), add a zero = a;
  mult_lident : forall (a : A), mult one a = a;
  mult_rident : forall (a : A), mult a one = a;
  zero_rannihilates : forall (a : A), mult a zero = zero;
  zero_lannihilates : forall (a : A), mult zero a = zero;


  le : A -> A -> Prop;
  le_refl : forall (a : A), le a a;
  le_trans : forall (a b c : A), le a b -> le b c -> le a c;


  eqb : A -> A -> bool;
  eqb_eq : forall (a1 a2 : A), a1 = a2 <-> eqb a1 a2 = true;


  le_addl : forall (a1 a2 a3 : A), le a1 a2 -> le (add a3 a1) (add a3 a2);
  le_addr : forall (a1 a2 a3 : A), le a1 a2 -> le (add a1 a3) (add a2 a3)
}.

Parameter Q_POSR : POSR.

Notation Q := (A Q_POSR).

Notation Qzero := (zero Q_POSR).

Notation Qone := (one Q_POSR).

Notation Qadd := (add Q_POSR).

Notation Qmult := (mult Q_POSR).

Notation Qle := (le Q_POSR).

Notation Qle_refl := (le_refl Q_POSR).

Notation Qle_trans := (le_trans Q_POSR).

Notation Qadd_lident := (add_lident Q_POSR).

Notation Qadd_rident := (add_rident Q_POSR).

Notation Qmult_lident := (mult_lident Q_POSR).

Notation Qmult_rident := (mult_rident Q_POSR).

Notation Qzero_rannihilates := (zero_rannihilates Q_POSR).

Notation Qzero_lannihilates := (zero_lannihilates Q_POSR).

Notation Qeqb := (eqb Q_POSR).

Notation Qeqb_eq := (eqb_eq Q_POSR).

Notation Qle_addl := (le_addl Q_POSR).

Notation Qle_addr := (le_addr Q_POSR).

Definition gradeVec n := fin n -> Q.

Definition gradeVecAdd {n} (γ1 γ2 : gradeVec n) :=
  fun (i : fin n) => Qadd (γ1 i) (γ2 i).

Definition gradeVecScale {n} (q : Q) (γ : gradeVec n) :=
  fun (i : fin n) => Qmult q (γ i).

Definition gradeVecLe {n} (γ1 γ2 : gradeVec n) : Prop :=
  forall (i : fin n), Qle (γ1 i) (γ2 i).

Definition gradeVecZero (n : nat) : gradeVec n :=
  fun (i : fin n) => Qzero.

Arguments gradeVecZero {n}.

Definition gradeVecOne (n : nat) : gradeVec n :=
    fun (i : fin n) => Qone.

Arguments gradeVecOne {n}.

Notation "γ1 'Q+' γ2" := (gradeVecAdd γ1 γ2) (at level 60).

Notation "q 'Q*' γ" := (gradeVecScale q γ) (at level 50).

Notation "γ1 'Q<=' γ2" := (gradeVecLe γ1 γ2) (at level 70).

Notation "0s" := gradeVecZero (at level 70).

Notation "1s" := gradeVecOne (at level 70).

Definition q_or_1 (q : Q) : Q :=
  if Qeqb q Qzero then Qone else q.

Definition nonzero_lb (q' : Q) (q : Q) :=
  (Qle q' q /\ q' <> Qzero) \/ Qzero = Qone.
