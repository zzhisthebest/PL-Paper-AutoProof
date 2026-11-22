Set Implicit Arguments.

Require Import Logic List Classes.Morphisms.

Import List Notations.

Require Export CBPV.Terms CBPV.Base CBPV.Semantics.

Import CommaNotation.

Reserved Notation "Gamma ⊢ c : A" (at level 80, c at level 99).

Reserved Notation "Gamma ⊩ v : A" (at level 80, v at level 99).

Definition ctx (n: nat) := fin n -> valtype.

Inductive value_typing {m: nat} (Gamma: ctx m) : value m -> valtype -> Type :=
| typeVar i : Gamma ⊩ var_value i : Gamma i
| typeUnit: Gamma ⊩ u : one
| typePair v1 v2 A1 A2:
    Gamma ⊩ v1 : A1 -> Gamma ⊩ v2 : A2 -> Gamma ⊩ pair v1 v2 : cross A1 A2
| typeSum A1 A2 (b: bool) v:
    Gamma ⊩ v : (if b then A1 else A2) -> Gamma ⊩ inj b v : Sigma A1 A2
| typeThunk c A:
    Gamma ⊢ c : A -> Gamma ⊩ thunk c : U A
where "Gamma ⊩ v : A" := (value_typing Gamma v A)


with computation_typing {m: nat} (Gamma: ctx m) : comp m -> comptype -> Type :=
| typeCone: Gamma ⊢ cu : cone
| typeLambda (c: comp (S m)) A B:
    A .: Gamma ⊢ c : B -> (Gamma ⊢ lambda c : A → B)
| typeLetin c1 c2 A B:
    Gamma ⊢ c1 : F A -> A .: Gamma ⊢ c2 : B -> Gamma ⊢ $ <- c1; c2 : B
| typeRet v A:
    Gamma ⊩ v : A -> Gamma ⊢ ret v : F A
| typeApp c v A B:
    Gamma ⊢ c : A → B -> Gamma ⊩ v : A -> Gamma ⊢ c v : B
| typeTuple c1 c2 B1 B2:
    Gamma ⊢ c1 : B1  -> Gamma ⊢ c2 : B2 -> Gamma ⊢ tuple c1 c2 : Pi B1 B2
| typeProj b c B1 B2:
    Gamma ⊢ c : Pi B1 B2 -> Gamma ⊢ proj b c : (if b then B1 else B2)
| typeForce v A:
    Gamma ⊩ v : U A -> Gamma ⊢ v! : A
| typeCaseZ v A: Gamma ⊩ v : zero -> Gamma ⊢ caseZ v : A
| typeCaseS v c1 c2 A1 A2 C:
    Gamma ⊩ v : Sigma A1 A2 ->
    A1, Gamma ⊢ c1 : C ->
    A2, Gamma ⊢ c2 : C ->
    Gamma ⊢ caseS v c1 c2 : C
| typeCaseP v c A B C:
    Gamma ⊩ v : A * B ->
    B, A, Gamma  ⊢ c : C ->
    Gamma ⊢ caseP v c : C
where "Gamma ⊢ c : A" := (@computation_typing _ Gamma c A).

Scheme value_typing_ind_2 := Minimality for value_typing Sort Prop
  with computation_typing_ind_2  := Minimality for computation_typing Sort Prop.

Scheme value_typing_ind_3 := Minimality for value_typing Sort Type
  with computation_typing_ind_3  := Minimality for computation_typing Sort Type.

Combined Scheme mutind_value_computation_typing from
         value_typing_ind_2, computation_typing_ind_2.

Scheme value_typing_ind_4 := Induction for value_typing Sort Prop
    with computation_typing_ind_4  := Induction for computation_typing Sort Prop.

Combined Scheme mutindt_value_computation_typing from
          value_typing_ind_4, computation_typing_ind_4.
