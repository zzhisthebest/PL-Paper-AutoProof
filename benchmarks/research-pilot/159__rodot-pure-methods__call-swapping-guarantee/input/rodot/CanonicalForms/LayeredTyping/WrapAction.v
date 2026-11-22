Set Implicit Arguments.

Require Import LibExtra DotTactics.

Require Import Coq.Program.Equality.

Require Import Types.

Require Import Logctx Logpath.

Inductive wrap_action: Set :=
  wrap_action_c(oc:logpath)(T U: typ): wrap_action.

Definition wrap_plan := list wrap_action.

Definition wrap_action_under(ocp: logpath)(wa: wrap_action) :=
  match wa with
  | wrap_action_c oc T U => wrap_action_c (logpath_extend ocp oc) T U
  end.

Definition wrap_plan_under ocp (wp: wrap_plan) := List.map (wrap_action_under ocp) wp.

Fixpoint wrap_action_logpath(wa: wrap_action) :=
  match wa with
  | wrap_action_c oc T U => oc
  end.

Definition wrap_action_separate ocp wa := logpath_separate ocp (wrap_action_logpath wa).

Definition wrap_plan_separate ocp (wp: wrap_plan) := List.Forall (wrap_action_separate ocp) wp.

Definition wrap_action_leaf wa :=
  match wa with
  | wrap_action_c oc T U => typ_notlog U
  end.

Definition wrap_plan_leaf (wp: wrap_plan) := List.Forall (wrap_action_leaf) wp.

Definition wrap_action_direct wa := (wrap_action_logpath wa) = logpath_nil.

Definition wrap_plan_direct (wp: wrap_plan) := List.Forall (wrap_action_direct) wp.

Inductive wrap_action_utyp: typ->wrap_action->typ->Prop :=
| wrap_action_utyp_c oc S T:
    wrap_action_utyp (logctx_typ oc S) (wrap_action_c (logctx_path oc) S T) (logctx_typ oc T)
.

Inductive wrap_plan_utyp: typ->wrap_plan->typ->Prop :=
| wrap_plan_utyp_nil T:
  wrap_plan_utyp T nil T
| wrap_plan_utyp_cons wp wa T S U:
  wrap_plan_utyp T wp S ->
  wrap_action_utyp S wa U ->
  wrap_plan_utyp T (cons wa wp) U
.

Class WrapActionDetermined (P: wrap_action -> Prop) :=
  wrap_action_determined wa wb T1 T2 U:
  P wa ->
  P wb ->
  wrap_action_direct wa ->
  wrap_action_direct wb ->
  wrap_action_utyp T1 wa U ->
  wrap_action_utyp T2 wb U ->
  wa = wb /\ T1 = T2.

Definition wrap_action_injective wa := (
  forall T1 T2 U,
  wrap_action_utyp T1 wa U ->
  wrap_action_utyp T2 wa U ->
  T1 = T2
).

Definition wrap_plan_injective (wp: wrap_plan) := List.Forall (wrap_action_injective) wp.

Class WrapActionClosed (P: wrap_action -> Prop) :=
  wrap_action_closed wa oc:
  (P (wrap_action_under oc wa)) ->
  P wa.

Class WrapActionClosedInv (P: wrap_action -> Prop) :=
  wrap_action_closed_inv wa oc:
  P wa ->
  (P (wrap_action_under oc wa)).

Definition wrap_action_leaf_typ (P: logpath -> Prop) (T: typ) :=
  forall op1 op2 oc,
    P (logpath_extend op1 op2) ->
    logpath_ctx T op2 oc ->
    op2 = logpath_nil.

Definition wrap_action_leaf_for (P: logpath -> Prop) wa :=
  match wa with
  | wrap_action_c op T U => (P op /\ wrap_action_leaf_typ P U)
  end.

Definition wrap_plan_leaf_for (P: logpath -> Prop)  (wp: wrap_plan) := List.Forall (wrap_action_leaf_for P) wp.
