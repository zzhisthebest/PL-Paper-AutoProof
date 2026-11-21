Set Implicit Arguments.

Require Import Sequences.

Require Import Coq.Program.Equality List String.

Require Import Definitions Binding RecordAndInertTypes.

Reserved Notation "G '⊢!v' v ':' T" (at level 40, v at level 59).

Inductive ty_val_p : ctx -> val -> typ -> Prop :=





| ty_all_intro_p : forall L G T t U,
    (forall x, x \notin L ->
      G & x ~ T ⊢ open_trm x t : open_typ x U) ->
    G ⊢!v λ(T) t : ∀(T) U





| ty_new_intro_p
     : forall (L : fset var) (G : env typ) (T : typ) (ds : defs),
       (forall x : var, x \notin L -> x; nil; G & x ~ open_typ x T ⊢ open_defs x ds :: open_typ x T) ->
       G ⊢!v ν(T)ds : μ T

where "G '⊢!v' v ':' T" := (ty_val_p G v T).

Reserved Notation "G '⊢!' p ':' T '⪼' U" (at level 40, p at level 59).

Inductive precise_flow : ctx -> path -> typ -> typ -> Prop :=





| pf_bind : forall x G T,
      ok G ->
      binds x T G ->
      G ⊢! pvar x: T ⪼ T




  | pf_fld : forall G p a T U,
      G ⊢! p: T ⪼ typ_rcd {a ⦂ U} ->
      G ⊢! p•a : U ⪼ U




  | pf_open : forall p G T U,
      G ⊢! p: T ⪼ μ U ->
      G ⊢! p: T ⪼ open_typ_p p U




  | pf_and1 : forall p G T U1 U2,
      G ⊢! p: T ⪼ U1 ∧ U2 ->
      G ⊢! p: T ⪼ U1




  | pf_and2 : forall p G T U1 U2,
      G ⊢! p: T ⪼ U1 ∧ U2 ->
      G ⊢! p: T ⪼ U2

where "G '⊢!' p ':' T '⪼' U" := (precise_flow G p T U).
