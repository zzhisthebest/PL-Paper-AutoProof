Require Import String.

Require Import Coq.Structures.Equalities.

Require Import Coq.MSets.MSetInterface.

Require Import Arith.

Require Import Setoid.

Require Import SystemF.

Require Import Coq.Program.Equality.

Require Export Subtyping.

Module MDisjointness
       (Import VarTyp : UsualDecidableTypeFull)
       (Import set : MSetInterface.S).

Module MSubtyping := MSubtyping(VarTyp)(set).

Export MSubtyping.

Definition hd (p : PTyp) : nat :=
  match p with
  | PInt       => 0
  | Fun t1 t2  => 1
  | ForAll d t => 2
  | Rec l t    => 3
  | Top        => 4
  | PBVarT n   => 5
  | PFVarT v   => 6
  | And t1 t2  => 7
  end.

Definition OrthoAx (t1 t2 : PTyp) : Prop :=
  (hd t1 < 4 /\ hd t2 < 4 /\ not (hd t1 = hd t2)).

Inductive Ortho : context TyEnvSource -> PTyp -> PTyp -> Prop :=
  | OAnd1 : forall Gamma t1 t2 t3, Ortho Gamma t1 t3 -> Ortho Gamma t2 t3 -> Ortho Gamma (And t1 t2) t3
  | OAnd2 : forall Gamma t1 t2 t3, Ortho Gamma t1 t2 -> Ortho Gamma t1 t3 -> Ortho Gamma t1 (And t2 t3)
  | OFun  : forall Gamma t1 t2 t3 t4, Ortho Gamma t2 t4 -> Ortho Gamma (Fun t1 t2) (Fun t3 t4)
  | OForAll : forall L Gamma d1 d2 t1 t2,
                (forall x, not (In x L) -> Ortho (extend x (TyDis (And d1 d2)) Gamma)
                                           (open_typ_source t1 (PFVarT x))
                                           (open_typ_source t2 (PFVarT x))) ->
                PType (And d1 d2) ->
                Ortho Gamma (ForAll d1 t1) (ForAll d2 t2)
  | OVar : forall Gamma x ty A, List.In (x,TyDis A) Gamma ->
                       usub A ty ->
                       PType ty ->
                       Ortho Gamma (PFVarT x) ty
  | OVarSym : forall Gamma x ty A, List.In (x,TyDis A) Gamma ->
                          usub A ty ->
                          PType ty ->
                          Ortho Gamma ty (PFVarT x)
  | OTop1 : forall Gamma t, Ortho Gamma Top t
  | OTop2 : forall Gamma t, Ortho Gamma t Top
  | ORecNeq : forall Gamma l1 l2 t1 t2, l1 <> l2 -> Ortho Gamma (Rec l1 t1) (Rec l2 t2)
  | ORecEq : forall Gamma l t1 t2, Ortho Gamma t1 t2 -> Ortho Gamma (Rec l t1) (Rec l t2)
  | OAx : forall Gamma t1 t2, OrthoAx t1 t2 -> Ortho Gamma t1 t2.

Definition OrthoS (A B : PTyp) := not (exists C, Sub A C /\ Sub B C).

End MDisjointness.
