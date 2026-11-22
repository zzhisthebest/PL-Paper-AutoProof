From Stdlib Require Import List.
Import ListNotations.

Require Export Poulet4.Utils.AList Poulet4.Utils.ForallMap Coq.Classes.EquivDec.

Section Util.

Context {K V: Type}
          {R : Relation_Definitions.relation K}
          `{HKR: EqDec K R}.

Fixpoint remove_first (key : K) (l : list (K * V)) : list (K * V) :=
    match l with
    | [] => []
    | (k, v) :: l => if HKR key k then l else (k, v) :: remove_first key l
    end.

End Util.

Section ALL.

Variables
    (K U W : Type)
    (R: Relation_Definitions.relation K).

Context `{HKR: EqDec K R}.

Variable P : U -> W -> Prop.

End ALL.

Section Rel.

Context {K A B : Type} {R: Relation_Definitions.relation K}
          `{H: Equivalence K R} {KEqDec: EqDec K R}.

Section Map.

Variable (f : A -> B).

Definition map_values  : AList K A R -> AList K B R :=
      List.map (fun '(k,a) => (k,f a)).

End Map.

Section Relate.

Variable Q : A -> B -> Prop.

End Relate.

End Rel.
