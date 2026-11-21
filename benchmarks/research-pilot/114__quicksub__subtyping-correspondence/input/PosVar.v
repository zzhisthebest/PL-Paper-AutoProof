Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Export Variance.

Inductive posvar: IsoMode -> atom -> typ -> typ -> Prop :=
| pos_nat: forall X m,
    posvar m X typ_nat typ_nat
| pos_top: forall X A m,
    type A ->
    posvar m X A typ_top
| pos_top_flip: forall X A m,
    type A ->
    posvar m X typ_top A
| pos_fvar_x: forall X,
    posvar Pos X (typ_fvar X) (typ_fvar X)
| pos_fvar_y: forall X Y m,
    X <> Y ->
    posvar m X (typ_fvar Y) (typ_fvar Y)
| pos_arrow: forall X m A1 A2 B1 B2,
    posvar (flip_im m) X B1 A1 ->
    posvar m X A2 B2 ->
    posvar m X (typ_arrow A1 A2) (typ_arrow B1 B2)
| pos_rec: forall X m A B L,
    (forall Y, Y \notin L \u {{X}} ->
               posvar m X (open_tt A Y) (open_tt B Y)) ->
     (forall Y, Y \notin L \u {{X}} ->
               posvar Pos Y (open_tt A Y) (open_tt B Y)) ->
    posvar m X (typ_mu A) (typ_mu B)
| pos_rec_t : forall A X m L,
    X \notin fv_tt A ->
    (forall Y, Y \notin L \u {{X}} ->
               type (open_tt A Y)) ->
    posvar m X (typ_mu A) (typ_mu A).
