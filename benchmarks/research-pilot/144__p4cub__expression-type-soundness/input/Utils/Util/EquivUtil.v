Require Export Coq.Numbers.BinNums Coq.Bool.Bool Poulet4.Utils.Util.ListUtil.

Require Import Coq.micromega.Lia.

Require Import String.

Notation "a '&&&&' b"
  := (if a then if b then true else false else false)
       (at level 60, right associativity).

Notation "a '||||' b"
  := (if a then true else if b then true else false)
       (at level 70, right associativity).

Section ListStuff.

Context {A : Type} {HED : EqDec A eq}.

Fixpoint eqb_list (l1 l2 : list A) : bool :=
    match l1, l2 with
    | []     , []      => true
    | a1 :: l1, a2 :: l2 => equiv_dec a1 a2 &&&& eqb_list l1 l2
    | _      , _       => false
    end.

End ListStuff.

Section Forall2_Equivalence.

Context {A : Type}.

Variable R : A -> A -> Prop.

Context `{Equivalence A R}.

End Forall2_Equivalence.

Variant predop {A : Type} (P : A -> Prop) : option A -> Prop :=
| predop_none : predop P None
| predop_some (a : A) : P a -> predop P (Some a).

Section Relop.

Context {A B : Type}.

Variable R : A -> B -> Prop.

Variant relop : option A -> option B -> Prop :=
  | relop_none : relop None None
  | relop_some a b : R a b -> relop (Some a) (Some b).

End Relop.

Section Relop.

End Relop.

Section Relop.

Context {A : Type}.

Variable R : A -> A -> Prop.

Context `{HAR : Equivalence A R}.

End Relop.

Section ProdEquivalence.

Context {A B : Type}.

Variable RA : A -> A -> Prop.

Variable RB : B -> B -> Prop.

Context `{Equivalence A RA}.

Context `{Equivalence B RB}.

Let RAB ab1 ab2 := RA (fst ab1) $ fst ab2 /\ RB (snd ab1) $ snd ab2.

End ProdEquivalence.

Global Instance PositiveEqDec : EqDec positive eq := { equiv_dec := BinPos.Pos.eq_dec }.

Global Instance NEqDec : EqDec N eq := { equiv_dec := BinNat.N.eq_dec }.

Global Instance ZEqDec : EqDec Z eq := { equiv_dec := BinInt.Z.eq_dec }.

Global Instance StringEqDec : EqDec String.string eq := { equiv_dec := string_dec }.
