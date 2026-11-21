Require Import Language.

Inductive erased_sort : sort -> Prop :=
| erased_Tm : forall a, erased_tm a -> erased_sort (Tm a)
| erased_Co : forall a b A, erased_tm a -> erased_tm b -> erased_tm A -> erased_sort (Co (Eq a b A)).

Definition erased_context : context -> Prop :=
  Forall (fun p => match p with (a,s) => erased_sort s end).

Definition Good (G : context) (D : available_props):=
  erased_context G /\
  forall c1 A B1 T1,
    binds c1 (Co (Eq A B1 T1)) G
    -> c1 `in` D
    -> exists C, Par G D A C /\ Par G D B1 C.

Definition AnnGood G D := Good (erase_context G) D.

Definition irrelevant G D (a : tm) :=
  (forall x A, binds x (Tm A) G -> x `notin` fv_tm_tm_tm (erase_tm a)) /\ AnnGood G D.

Theorem preservation : forall G a A, AnnTyping G a A -> forall a', head_reduction G a a' -> AnnTyping G a' A.

Theorem progress : forall G a A, irrelevant G (dom G) a -> AnnTyping G a A -> CoercedValue a \/ exists a', head_reduction G a a'.
