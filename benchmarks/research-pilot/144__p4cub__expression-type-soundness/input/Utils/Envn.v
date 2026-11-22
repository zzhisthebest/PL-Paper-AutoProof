Require Import Poulet4.Utils.Util.Utiliser.

Declare Custom Entry p4env.

Module Env.

Definition t (D T : Type) : Type := list (D * T).

Definition empty (D T : Type) : t D T := nil.

Section EnvDefs.

Context {D T : Type}.

Context {equiv_rel : D -> D -> Prop}.

Context {HEquiv : Equivalence equiv_rel}.

Context {HE : EqDec D equiv_rel}.

Fixpoint find (x: D) (e: t D T) : option T :=
    match e with
    | nil => None
    | (y, v) :: e' =>
      if HE x y
      then Some v
      else find x e'
    end.

Fixpoint consume (x: D) (e: t D T) : (option T * t D T) :=
    match e with
    | nil => (None, nil)
    | (y,v) :: e' =>
      if HE x y
      then (Some v, e')
      else
        match consume x e' with
        | (Some v, e'') => (Some v, (y,v) :: e'')
        | (None, e'') => (None, (y,v) :: e'')
        end
    end.

Definition bind (x : D) (v : T) (e : t D T) : t D T :=
    (x, v) :: e.

Definition remove (d : D) : t D T -> t D T :=
    List.filter (fun '(d',_) => if HE d d' then false else true).

Definition scope_shadow (e1 e2 : t D T) : t D T :=
    e1 ++ e2.

Definition gather (e: t D T) : list D -> list T :=
    List.fold_right
      (fun k acc =>
         match find k e with
         | Some v => v :: acc
         | None => acc
         end) [].

Fixpoint keys (e: t D T) : list D :=
    match e with
    | nil => nil
    | (y, v) :: e' =>
      let keys' := keys e' in
      match find y e' with
      | None => y::keys'
      | _ => keys'
      end
    end.

Definition sub_env (e1 e2 : t D T) : Prop :=
    forall k v,
      find k e1 = Some v -> find k e2 = Some v.

Definition eq_env (e1 e2 : t D T) : Prop :=
    sub_env e1 e2 /\ sub_env e2 e1.

Definition disjoint (e₁ e₂ : t D T) : Prop := forall k,
      (find k e₁ <> None -> find k e₂ = None) /\
      (find k e₂ <> None -> find k e₁ = None).

Definition disjoint_union (e₁ e₂ e₃ : t D T) : Prop :=
    disjoint e₁ e₂ /\ eq_env (e₁ ++ e₂) e₃.

Section Lemmas.

End Lemmas.

End EnvDefs.

Section MapKeys.

Context {A B T : Type}.

Variable (f : A -> B).

Definition map_keys : t A T -> t B T :=
    List.map (fun '(k, v) => (f k, v)).

Context {EA : EqDec A eq}.

Context {EB : EqDec B eq}.

End MapKeys.

Section MapVals.

Context {D U V : Type}.

Variable (f : U -> V).

Definition map_vals : t D U -> t D V :=
    List.map (fun '(k, v) => (k, f v)).

Context {R : D -> D -> Prop}.

Context {RE: Equivalence R}.

Context {RED: EqDec D R}.

End MapVals.

Module EnvNotations.

Notation "e1 '⊆' e2"
    := (sub_env e1 e2)
         (at level 80, no associativity) : type_scope.

Notation "e1 '≝' e2"
    := (eq_env e1 e2)
         (at level 80, no associativity) : type_scope.

Notation "'!{' env '}!'" := env (env custom p4env at level 99).

Notation "x" := x (in custom p4env at level 0, x constr at level 0).

Notation "'∅'" := (empty _ _) (in custom p4env at level 0, no associativity).

Notation "x ↦ v ';;' e"
    := (bind x v e)
         (in custom p4env at level 40, e custom p4env,
             right associativity).

Notation "e1 ≪ e2"
           := (scope_shadow e1 e2)
                (in custom p4env at level 41, e1 custom p4env,
                    e2 custom p4env, right associativity).

End EnvNotations.

End Env.
