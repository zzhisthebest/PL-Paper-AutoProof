Require Import Coq.Numbers.BinNums.

Require Import Coq.Classes.EquivDec.

Require Import Coq.ZArith.BinInt.

Require Import Coq.NArith.BinNat.

Record t (tags_t: Type) :=
  { tags: tags_t;
    value: Z;
    width_signed: option (N * bool); }.

Arguments tags [tags_t] _.

Arguments value [tags_t] _.

Arguments width_signed [tags_t] _.

Global Instance ZEqDec : EqDec Z eq :=
  { equiv_dec := Z.eq_dec }.

Global Instance NEqDec : EqDec N eq :=
  { equiv_dec := N.eq_dec }.

Section IntEquiv.

Context {tags_t : Type}.

Definition eqb (n1 n2 : t tags_t) : bool :=
    if value n1 == value n2 then
      if width_signed n1 == width_signed n2 then true else false
    else false.

Definition equiv (n1 n2 : t tags_t) : Prop :=
    value n1 = value n2 /\ width_signed n1 = width_signed n2.

End IntEquiv.

Section IntEquivDec.

Variable (tags_t : Type).

End IntEquivDec.

Module P4IntArithmetic.

Section Arithmetic.

Context {tags_t : Type}.

Definition eq_width (n1 n2 : t tags_t) : Prop := width_signed n1 = width_signed n2.

Definition add_p4int_assume (n1 n2 : t tags_t) : t tags_t :=
      {| tags := tags n1;
         value := value n1 + value n2;
         width_signed := width_signed n1 |}.

End Arithmetic.

End P4IntArithmetic.
