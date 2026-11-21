Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Export PosVar.

Definition mode_xor (m1 m2 : IsoMode) : IsoMode :=
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

Definition mode_choose {A:Type} im im_x (C D:A) :=
  match im, im_x with
  | Pos, Pos => C
  | Pos, Neg => D
  | Neg, Pos => D
  | Neg, Neg => C
  end.

Definition well_bind_env im (E:env) (A B : typ) :=
  (forall X im_x,
    (binds X (bind_sub im_x) E -> posvar (mode_xor im im_x) X A B)).

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
