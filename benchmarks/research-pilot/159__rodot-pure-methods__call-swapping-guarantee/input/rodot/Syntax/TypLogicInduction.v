Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Types Orctx Logctx OrctxLogctx Logpath LogpathOrder.

Require Import Coq.Program.Equality.

Inductive typ_notorand: typ-> Prop :=
| typ_notorand_not T:
  typ_notor T ->
  typ_notand T ->
  typ_notorand T
| typ_notorand_or T U:
  typ_notorand T ->
  typ_notorand U ->
  typ_notorand (typ_or T U)
.

Inductive typ_notorand_le: logpath -> typ -> Prop :=
| typ_notorand_le_nil T:
  typ_notorand_le logpath_nil T
| typ_notorand_orl op T U:
  typ_notorand_le op T ->
  typ_notorand_le (logpath_orl op) (typ_or T U)
| typ_notorand_orr op T U:
  typ_notorand T ->
  typ_notorand_le op U ->
  typ_notorand_le (logpath_orr op) (typ_or T U)
.

Inductive orctx_notorand_le: orctx->Prop :=
| orctx_notorand_le_nil:
  orctx_notorand_le orctx_nil
| orctx_notorand_le_l oc T:
  orctx_notorand_le oc ->
  orctx_notorand_le (orctx_l oc T)
| orctx_notorand_le_r oc T:
  typ_notorand T ->
  orctx_notorand_le oc ->
  orctx_notorand_le (orctx_r T oc).

Fixpoint typ_logic_count (T: typ): nat :=
  match T with
  | typ_and T1 T2 => 1 + (typ_logic_count T2) + (typ_logic_count T1)
  | typ_or T1 T2 => 1 + (typ_logic_count T2) + (typ_logic_count T1)
  | _ => 0
  end.

Fixpoint typ_orand_count (T: typ): nat :=
  match T with
  | typ_and T1 T2 => 1
  | typ_or T1 T2 => (typ_orand_count T2) + (typ_orand_count T1)
  | _ => 0
  end.

Fixpoint typ_logic_and_count (T: typ): nat :=
  match T with
  | typ_and T1 T2 => 1 + (typ_logic_and_count T2) + (typ_logic_and_count T1)
  | typ_or T1 T2 => (typ_logic_and_count T2) + (typ_logic_and_count T1)
  | _ => 0
  end.

Fixpoint typ_orand_index T: nat :=
  match T with
  | typ_and T1 T2 => 1
  | typ_or T1 T2 =>
      let nL := (typ_orand_index T1) in
      match nL with

      | 0 => 1 + (typ_orand_index T2)

      | _ => 1 + nL + (typ_logic_count T2)
      end
  | _ => 0
  end.

Fixpoint typ_orand_leftmost_orctx T: orctx :=
  match T with
  | typ_or T1 T2 =>
      let nL := (typ_orand_count T1) in
      match nL with

      | 0 => orctx_r T1 (typ_orand_leftmost_orctx T2)

      | _ => orctx_l (typ_orand_leftmost_orctx T1) T2
      end
  | _ => orctx_nil
  end.

Inductive ty_dist_eq  : typ -> typ -> Prop :=
| ty_dist_eq_refl   T:

  ty_dist_eq   T T
| ty_dist_eq_or   T1 T2 U1 U2:
  ty_dist_eq   T1 U1 ->
  ty_dist_eq   T2 U2 ->
  ty_dist_eq   (typ_or T1 T2) (typ_or U1 U2)
| ty_dist_eq_and1   T1 T2 U:
  ty_dist_eq   T1 U ->
  ty_dist_eq   T2 U ->
  ty_dist_eq   (typ_and T1 T2) U
| ty_dist_eq_andl2   T1 T2 U:
  ty_dist_eq   U T1 ->
  ty_dist_eq   U (typ_and T1 T2)
| ty_dist_eq_andr2   T1 T2 U:
  ty_dist_eq   U T2 ->
  ty_dist_eq   U (typ_and T1 T2)
.
