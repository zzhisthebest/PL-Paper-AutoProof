Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Export AmberBase.

Fixpoint mode_xor (m1 m2 : Mode) : Mode :=
  match m1 with
  | Pos => match m2 with
           | Pos => Pos
           | Neg => Neg
           end
  | Neg => match m2 with
           | Pos => Neg
           | Neg => Pos
           end
  end.

Inductive typePairR : typ -> typ -> Prop :=
| tp_nat:
    typePairR  typ_nat typ_nat
| tp_top: forall  A ,
    type A ->
    typePairR  A typ_top
| tp_top_flip: forall A ,
    type A ->
    typePairR  typ_top A
| tp_fvar_x: forall X,
    typePairR (typ_fvar X) (typ_fvar X)
| tp_arrow: forall  A1 A2 B1 B2,
    typePairR  B1 A1 ->
    typePairR  A2 B2 ->
    typePairR  (typ_arrow A1 A2) (typ_arrow B1 B2)
| tp_rec: forall  A B L,
    (forall X, X \notin L ->
               typePairR (open_tt A X) (open_tt B X)) ->
    typePairR (typ_mu A) (typ_mu B).
