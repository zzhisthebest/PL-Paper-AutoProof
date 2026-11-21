From Stdlib Require Import List.

Require Import Stdlib.Classes.RelationClasses.

Import ListNotations.

Require Import Syntax Notations Helpers.

Inductive method_scope_subtype : method_scope -> method_scope -> Prop :=
  | method_subtyping_refl : forall mt,
      method_scope_subtype mt mt
  | method_cs_as : method_scope_subtype ConcreteState AbstractState
  | method_rs_as : method_scope_subtype ReadonlyState AbstractState
  | method_ts_as : method_scope_subtype TransitiveState AbstractState
  | method_ts_cs : method_scope_subtype TransitiveState ConcreteState
  | method_ts_rs : method_scope_subtype TransitiveState ReadonlyState
  .

Inductive q_subtype : q -> q -> Prop :=
  | q_refl : forall q1
      (Hnot_lost : q1 <> Lost),
      q_subtype q1 q1
  | q_rd : forall q1,
      q_subtype q1 RO
  | q_bot : forall q1,
      q_subtype Bot q1
where "q1 ⊑ q2" := (q_subtype q1 q2).

Definition parent_lookup (CT : class_table) (C : class_name) : option class_name :=
  match find_class CT C with
  | Some def => super (signature def)
  | None => None
  end.

Inductive base_subtype : class_table -> class_name -> class_name -> Prop :=
  | base_refl : forall (CT : class_table) (C : class_name)
      (Hdom : C < dom CT),
      base_subtype CT C C
  | base_trans : forall (CT : class_table) (C D E : class_name)
      (Hsub1 : base_subtype CT C D)
      (Hsub2 : base_subtype CT D E),
      base_subtype CT C E
  | base_extends : forall (CT : class_table) (C D : class_name)
      (Hdom_C  : C < dom CT)
      (Hdom_D  : D < dom CT)
      (Hparent : parent_lookup CT C = Some D),
      base_subtype CT C D.

Inductive qualified_type_subtype : class_table -> qualified_type -> qualified_type -> Prop :=
  | qtype_sub : forall CT qt1 qt2
      (Hdom1  : sctype qt1 < dom CT)
      (Hdom2  : sctype qt2 < dom CT)
      (Hqsub  : q_subtype (sqtype qt1) (sqtype qt2))
      (Hbsub  : base_subtype CT (sctype qt1) (sctype qt2)),
      qualified_type_subtype CT qt1 qt2
  | qtype_trans : forall CT qt1 qt2 qt3
      (Hsub12 : qualified_type_subtype CT qt1 qt2)
      (Hsub23 : qualified_type_subtype CT qt2 qt3),
      qualified_type_subtype CT qt1 qt3
  | qtype_refl : forall CT qt
      (Hdom      : sctype qt < dom CT)
      (Hnot_lost : sqtype qt <> Lost),
      qualified_type_subtype CT qt qt.
