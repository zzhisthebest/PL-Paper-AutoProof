Require Import Poulet4.Utils.Util.Utiliser Coq.Logic.FunctionalExtensionality.

Module Clmt.

Definition t (D T : Set) : Set := D -> option T.

Definition empty (D T : Set) : t D T := fun _ => None.

Section EnvDefs.

Context {D T : Set}.

Context {HE : EqDec D eq}.

Definition bind (x : D) (v : T) (e : t D T) : t D T :=
      fun y => if x == y then Some v else e y.

Definition remove (d : D) (e : t D T) : t D T :=
      fun y => if d == y then None else e y.

Definition gather (e: t D T) : list D -> list T :=
      List.fold_right
        (fun k acc =>
           match e k with
           | Some v => v :: acc
           | None => acc
           end) [].

Definition shadow (e1 e2 : t D T) : t D T :=
      fun d => match e1 d, e2 d with
            | Some _, Some v
            | Some v, None => Some v
            | _     , _    => None
            end.

Definition sub_env (e1 e2 : t D T) : Prop :=
      forall k v, e1 k = Some v -> e2 k = Some v.

Definition disjoint (e₁ e₂ : t D T) : Prop := forall k,
        (e₁ k <> None -> e₂ k = None) /\
        (e₂ k <> None -> e₁ k = None).

Definition union (e₁ e₂ : t D T) : t D T :=
      fun y => match e₁ y with
            | Some v => Some v
            | None   => e₂ y
            end.

Definition strip (e₁ e₂ : t D T) : t D T :=
      fun y => match e₁ y with
            | Some _ => None
            | None   => e₂ y
            end.

Definition disjoint_union (e₁ e₂ e₃ : t D T) : Prop :=
      disjoint e₁ e₂ /\ union e₁ e₂ = e₃.

Section Lemmas.

End Lemmas.

End EnvDefs.

Section MapVals.

Context {D U V : Set}.

Variable (f : U -> V).

Definition map_vals (e : t D U) : t D V :=
      fun k => e k >>| f.

End MapVals.

Module Notations.

Declare Scope climate_scope.

Delimit Scope climate_scope with climate.

Notation "e1 '⊆' e2"
      := (sub_env e1 e2)
           (at level 80, no associativity) : type_scope.

Notation "'∅'"
      := (empty _ _) (at level 0, no associativity) : climate_scope.

Notation "x ↦ v ',,' e"
      := (bind x v e)
           (at level 41, right associativity) : climate_scope.

Notation "e1 ≪ e2"
      := (shadow e1 e2)
           (at level 41, right associativity) : climate_scope.

End Notations.

End Clmt.
