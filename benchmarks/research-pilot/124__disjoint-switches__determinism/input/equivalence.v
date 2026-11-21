Require Import Metalib.Metatheory.

Require Import Lia.

Inductive typ : Set :=
 | t_int : typ
 | t_top : typ
 | t_bot : typ
 | t_arrow : typ -> typ -> typ
 | t_union : typ -> typ -> typ
 | t_and : typ -> typ -> typ
 | t_unit : typ
 | t_prim (n:var).

Definition envp : Set := list ( atom * typ ).

Inductive wft (PG:envp) : typ -> Prop :=
  | wft_top :
      wft PG t_top
  | wft_bot :
      wft PG t_bot
  | wft_int :
      wft PG t_int
  | wft_arrow : forall A B,
      wft PG A ->
      wft PG B ->
      wft PG (t_arrow A B)
  | wft_or : forall A B,
      wft PG A ->
      wft PG B ->
      wft PG (t_union A B)
  | wft_and : forall A B,
      wft PG A ->
      wft PG B ->
      wft PG (t_and A B)
  | wft_unit :
      wft PG t_unit
  | wft_prim : forall i A,
      binds i A PG ->
      wft PG (t_prim i).

Inductive okenvp : envp -> Prop :=
  | okenvp_empty :
      okenvp nil
  | okenvp_cons : forall (PG:envp) (i:var),
      okenvp PG ->
      i `notin` (dom PG) ->
      okenvp ((i, t_top) :: PG)
  | okenvp_sub : forall (PG:envp) (i j:var),
      okenvp PG ->
      wft PG (t_prim j) ->
      i `notin` (dom PG) ->
      okenvp ((i, (t_prim j)) :: PG).

Inductive declarative_subtyping (PG: envp) : typ -> typ -> Prop :=
 | DS_refl : forall (A:typ),
     okenvp PG ->
     wft PG A ->
     declarative_subtyping PG A A
 | DS_trans : forall (A C B:typ),
     declarative_subtyping PG A B ->
     declarative_subtyping PG B C ->
     declarative_subtyping PG A C
 | DS_top : forall (A:typ),
     okenvp PG ->
     wft PG A ->
     declarative_subtyping PG A t_top
 | DS_bot : forall (A:typ),
     okenvp PG ->
     wft PG A ->
     declarative_subtyping PG t_bot A
 | DS_arrow : forall (A C B D:typ),
     declarative_subtyping PG B A ->
     declarative_subtyping PG C D ->
     declarative_subtyping PG (t_arrow A C) (t_arrow B D)
 | DS_and : forall (A B C:typ),
     declarative_subtyping PG A B ->
     declarative_subtyping PG A C ->
     declarative_subtyping PG A (t_and B C)
 | DS_andl : forall (A B:typ),
     okenvp PG ->
     wft PG A -> wft PG B ->
     declarative_subtyping PG (t_and A B) A
 | DS_andr : forall (A B:typ),
     okenvp PG ->
     wft PG A -> wft PG B ->
     declarative_subtyping PG (t_and A B) B
 | DS_or : forall (A B C:typ),
     declarative_subtyping PG A C ->
     declarative_subtyping PG B C ->
     declarative_subtyping PG (t_union A B) C
 | DS_orl : forall (A B:typ),
     okenvp PG ->
     wft PG A -> wft PG B ->
     declarative_subtyping PG A (t_union A B)
 | DS_orr : forall (B A:typ),
     okenvp PG ->
     wft PG A -> wft PG B ->
     declarative_subtyping PG B (t_union A B)
 | DS_distArr : forall (A B1 B2:typ),
     okenvp PG ->
     wft PG A -> wft PG B1 -> wft PG B2 ->
     declarative_subtyping PG (t_and  (t_arrow A B1)   (t_arrow A B2) ) (t_arrow A (t_and B1 B2))
| DS_distArrU : forall (A1 B A2:typ),
     okenvp PG ->
     wft PG A1 -> wft PG A2 -> wft PG B ->
     declarative_subtyping PG (t_and  (t_arrow A1 B)   (t_arrow A2 B) ) (t_arrow (t_union A1 A2) B)
 | DS_distOr : forall (A1 B A2:typ),
     okenvp PG ->
     wft PG A1 -> wft PG A2 -> wft PG B ->
     declarative_subtyping PG (t_and  (t_union A1 B)   (t_union A2 B) ) (t_union  (t_and A1 A2)  B)
 | DS_prim : forall i A,
     okenvp PG ->
     binds i A PG ->
     declarative_subtyping PG (t_prim i) A.
