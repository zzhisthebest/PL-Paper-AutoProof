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

Inductive ordu : typ -> Prop :=
 | OU_top :
     ordu t_top
 | OU_bot :
     ordu t_bot
 | OU_int :
     ordu t_int
 | OU_arrow : forall (A B:typ),
     ordu (t_arrow A B)
 | OU_and : forall (A B:typ),
     ordu A ->
     ordu B ->
     ordu (t_and A B)
 | OU_null :
     ordu t_unit
 | OU_prim : forall (i:var),
     ordu (t_prim i).

Inductive ordi : typ -> Prop :=
 | OI_top :
     ordi t_top
 | OI_bot :
     ordi t_bot
 | OI_int :
     ordi t_int
 | OI_arrow : forall (A B:typ),
     ordu A ->
     ordi B ->
     ordi (t_arrow A B)
 | OI_or : forall (A B:typ),
     ordi A ->
     ordi B ->
     ordi (t_union A B)
 | OI_null :
     ordi t_unit
 | OI_prim : forall (i:var),
     ordi (t_prim i).

Inductive splu : typ -> typ -> typ -> Prop :=
 | SpU_or : forall (A B:typ),
     splu (t_union A B) A B
 | SpU_andl : forall (A B A1 A2:typ),
     splu A A1 A2 ->
     splu (t_and A B) (t_and A1 B) (t_and A2 B)
 | SpU_andr : forall (A B B1 B2:typ),
     ordu A ->
     splu B B1 B2 ->
     splu (t_and A B) (t_and A B1) (t_and A B2).

Inductive spli : typ -> typ -> typ -> Prop :=
 | SpI_and : forall (A B:typ),
     spli (t_and A B) A B
 | SpI_arrow : forall (A B C D:typ),
     spli B C D ->
     spli (t_arrow A B) (t_arrow A C) (t_arrow A D)
 | SpI_arrowUnion : forall (A D B C:typ),
     ordi D ->
     splu A B C ->
     spli (t_arrow A D) (t_arrow B D) (t_arrow C D)
 | SpI_orl : forall (A B A1 A2:typ),
     spli A A1 A2 ->
     spli (t_union A B) (t_union A1 B) (t_union A2 B)
 | SpI_orr : forall (A B B1 B2:typ),
     ordi A ->
     spli B B1 B2 ->
     spli (t_union A B) (t_union A B1) (t_union A B2).

Inductive algo_sub : envp -> typ -> typ -> Prop :=
 | AS_refl : forall PG A,
     okenvp PG ->
     wft PG A ->
     algo_sub PG A A
 | AS_prim_neq : forall PG i A n1 n2,
     okenvp ((i, A) :: PG) ->

     i <> n1 ->
     algo_sub PG (t_prim n1) (t_prim n2) ->
     algo_sub (((i, A))::PG) (t_prim n1) (t_prim n2)
 | AS_prim_eq : forall PG j n1 n2,
     okenvp (((n1,t_prim j))::PG) ->

     algo_sub PG (t_prim j) (t_prim n2) ->
     algo_sub (((n1,t_prim j))::PG) (t_prim n1) (t_prim n2)
 | AS_top : forall PG (A:typ),
     okenvp PG ->
     wft PG A ->
     algo_sub PG A t_top
 | AS_bot : forall PG (A:typ),
     okenvp PG ->
     wft PG A ->
     algo_sub PG t_bot A
 | AS_arrow : forall PG (A1 A2 B1 B2:typ),
     algo_sub PG B1 A1 ->
     algo_sub PG A2 B2 ->
     algo_sub PG (t_arrow A1 A2) (t_arrow B1 B2)
 | AS_and : forall PG (A B B1 B2:typ),
     spli B B1 B2 ->
     algo_sub PG A B1 ->
     algo_sub PG A B2 ->
     algo_sub PG A B
 | AS_andl : forall PG (A B A1 A2:typ),
     wft PG A2 ->
     spli A A1 A2 ->
     algo_sub PG A1 B ->
     algo_sub PG A B
 | AS_andr : forall PG (A B A1 A2:typ),
     wft PG A1 ->
     spli A A1 A2 ->
     algo_sub PG A2 B ->
     algo_sub PG A B
 | AS_or : forall PG (A B A1 A2:typ),
     splu A A1 A2 ->
     algo_sub PG A1 B ->
     algo_sub PG A2 B ->
     algo_sub PG A B
 | AS_orl : forall PG (A B B1 B2:typ),
     wft PG B2 ->
     splu B B1 B2 ->
     algo_sub PG A B1 ->
     algo_sub PG A B
 | AS_orr : forall PG (A B B1 B2:typ),
     wft PG B1 ->
     splu B B1 B2 ->
     algo_sub PG A B2 ->
     algo_sub PG A B.

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_int => 1
    | t_top => 1
    | t_bot => 1
    | t_unit => 1
    | t_prim _ => 1
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_and A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_union A2 B1 => 1 + (size_typ A2) + (size_typ B1)
  end.

Fixpoint size_envp (G : envp) := match G with
                                 | nil => 0
                                 | (i, A) :: G => size_envp G + size_typ A + 1
                                     end.

Theorem dsub2asub: forall G A B,
    declarative_subtyping G A B <-> algo_sub G A B.

Theorem decidability : forall G A B,
    algo_sub G A B \/ not (algo_sub G A B).
