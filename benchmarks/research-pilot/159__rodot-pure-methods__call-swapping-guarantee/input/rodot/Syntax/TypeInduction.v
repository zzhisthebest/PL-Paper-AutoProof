Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Types SyntaxClasses Objctx.

Require Import Lia.

Inductive typ_icp_ind: typ -> Prop :=

| typ_icp_ind_top: typ_icp_ind typ_top
| typ_icp_ind_bot: typ_icp_ind typ_bot
| typ_icp_ind_rcd D: typ_icp_ind (typ_rcd D)

| typ_icp_ind_and T1 T2:
    typ_icp_ind T1 ->
    typ_icp_ind T2 ->
    typ_icp_ind (typ_and T1 T2)
| typ_icp_ind_or T1 T2:
    typ_icp_ind T1 ->
    typ_icp_ind T2 ->
    typ_icp_ind (typ_or T1 T2)
| typ_icp_ind_sel x L y: typ_icp_ind (typ_sel x L y)

| typ_icp_ind_bnd T:
    (forall x, typ_icp_ind (open x T)) ->
    typ_icp_ind (typ_bnd T)
| typ_icp_ind_fun T1 T2: typ_icp_ind (typ_fun T1 T2)
| typ_icp_ind_nocap: typ_icp_ind (typ_nocap).

Fixpoint typ_icp_ind_height (T: typ): nat :=
  match T with

  | typ_bnd T => S (typ_icp_ind_height T)

  | typ_and T1 T2 => S (max (typ_icp_ind_height T1) (typ_icp_ind_height T2))
  | typ_or T1 T2 => S (max (typ_icp_ind_height T1) (typ_icp_ind_height T2))

  | _ => 0
  end.

Inductive typ_opening_ind: typ -> Prop :=

| typ_opening_ind_top: typ_opening_ind typ_top
| typ_opening_ind_bot: typ_opening_ind typ_bot
| typ_opening_ind_fun T1 T2:
    typ_opening_ind T1 ->
    (forall x, typ_opening_ind (open x T2)) ->
    typ_opening_ind (typ_fun T1 T2)
| typ_opening_ind_fld a T1 T2:
    typ_opening_ind T1 ->
    typ_opening_ind T2 ->
    typ_opening_ind (typ_rcd (dec_fld a T1 T2))
| typ_opening_ind_typ A T1 T2:
    (forall x, typ_opening_ind (open x T1)) ->
    (forall x, typ_opening_ind (open x T2)) ->
    typ_opening_ind (typ_rcd (dec_typ A T1 T2))
| typ_opening_ind_met M T1 T2 T3:
    (forall x, typ_opening_ind (open x T1)) ->
    typ_opening_ind T2 ->
    (forall x y, typ_opening_ind (open_met x y T1)) ->
    typ_opening_ind (typ_rcd (dec_met M T1 T2 T3))

| typ_opening_ind_and T1 T2:
    typ_opening_ind T1 ->
    typ_opening_ind T2 ->
    typ_opening_ind (typ_and T1 T2)
| typ_opening_ind_or T1 T2:
    typ_opening_ind T1 ->
    typ_opening_ind T2 ->
    typ_opening_ind (typ_or T1 T2)
| typ_opening_ind_sel x L y: typ_opening_ind (typ_sel x L y)

| typ_opening_ind_bnd T:
    (forall x, typ_opening_ind (open x T)) ->
    typ_opening_ind (typ_bnd T)
| typ_opening_ind_nocap: typ_opening_ind (typ_nocap).

Fixpoint typ_opening_ind_height (T: typ): nat :=
  match T with

  | typ_bnd T => S (typ_opening_ind_height T)

  | typ_and T1 T2 => S (max (typ_opening_ind_height T1) (typ_opening_ind_height T2))
  | typ_or T1 T2 => S (max (typ_opening_ind_height T1) (typ_opening_ind_height T2))
  | typ_fun T1 T2 => S (max (typ_opening_ind_height T1) (typ_opening_ind_height T2))
  | typ_rcd (dec_fld a T1 T2) => S (max (typ_opening_ind_height T1) (typ_opening_ind_height T2))
  | typ_rcd (dec_typ A T1 T2) => S (max (typ_opening_ind_height T1) (typ_opening_ind_height T2))
  | typ_rcd (dec_met m T1 T2 T3) => S (max (max (typ_opening_ind_height T1) (typ_opening_ind_height T2)) (typ_opening_ind_height T3))

  | _ => 0
  end.
