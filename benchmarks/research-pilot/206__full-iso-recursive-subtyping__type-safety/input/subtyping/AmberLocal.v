Require Import Metalib.Metatheory.

Require Import Program.Equality.

Require Export Rules.

Require Export Infra.

Require Export AmberBase.

Require Import Lia.

Inductive WFC :  typ -> nat -> Prop :=
| WC_nat: forall k,
    WFC typ_nat k
| WF_top: forall k,
    WFC typ_top k
| WF_fvar: forall X k,
    WFC (typ_fvar X) k
| WF_bvar: forall b k,
    b < k ->
    WFC (typ_bvar b) k
| WF_arrow: forall A B k,
    WFC A k ->
    WFC B k ->
    WFC (typ_arrow A B) k
| WF_rec: forall A n,
    WFC A (S n) ->
    WFC (typ_mu A) n
.

Fixpoint close_tt_rec (K : nat) (Z : atom) (T : typ) {struct T} : typ :=
  match T with
  | typ_nat         => typ_nat
  | typ_top         => typ_top
  | typ_bvar J      => typ_bvar J
  | typ_fvar X      => if X == Z then typ_bvar K else typ_fvar X
  | typ_arrow T1 T2 => typ_arrow (close_tt_rec K Z T1) (close_tt_rec K Z T2)
  | typ_mu T        => typ_mu (close_tt_rec (S K) Z T)
  end.

Definition close_tt T X := close_tt_rec 0 X T.

Fixpoint weight (T:typ) : nat :=
  match T with
  | typ_nat => 1
  | typ_top => 1
  | typ_fvar _ => 1
  | typ_bvar _ => 1
  | typ_arrow A B => 1 + weight A + weight B
  | typ_mu A => 1 + weight A
  end.
