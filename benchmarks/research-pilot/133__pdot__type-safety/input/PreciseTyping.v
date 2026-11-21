Set Implicit Arguments.

Require Import Sequences.

Require Import Coq.Program.Equality List.

Require Import Definitions Binding RecordAndInertTypes Replacement.

Require Export PreciseFlow.

Reserved Notation "G '⊢!!' p ':' T" (at level 40, p at level 59).

Reserved Notation "G '⊢!!!' p ':' T" (at level 40, p at level 59).

Inductive precise_typing2: ctx -> path -> typ -> Prop :=
| pt2: forall G p T U,
    G ⊢! p : T ⪼ U ->
    G ⊢!! p: U
| pt2_sngl_trans : forall G p q a U,
    G ⊢!! p : {{ q }} ->
    G ⊢!! q•a : U ->
    G ⊢!! p•a : {{ q•a }}
where "G '⊢!!' p ':' T" := (precise_typing2 G p T).

Inductive precise_typing3: ctx -> path -> typ -> Prop :=
| pt3: forall G p T,
    G ⊢!! p : T ->
    G ⊢!!! p: T
| pt3_sngl_trans : forall G p q T,
    G ⊢!! p : {{ q }} ->
    G ⊢!!! q : T ->
    G ⊢!!! p : T
where "G '⊢!!!' p ':' T" := (precise_typing3 G p T).

Inductive wf : ctx -> Prop :=
| wfe_empty :
    wf empty
| wfe_push G x T :
    wf G ->
    x # G ->
    (forall bs q, G & x ~ T ⊢! p_sel (avar_f x) bs : {{ q }}⪼ {{ q }}->
             exists U, G & x ~ T ⊢!! q : U) ->
    wf (G & x ~ T).

Definition typed_repl_comp_qp G T1 T2 :=
  exists p q U,
    G ⊢! p: {{ q }} ⪼ {{ q }} /\
    G ⊢!! q : U /\
    repl_typ q p T1 T2.

Definition repl_composition_qp G := star (typed_repl_comp_qp G).

Notation "G '⊢' T '⟿' U" := (repl_composition_qp G U T) (at level 40, T at level 59).

Inductive typed_path_repl_comp_qp: ctx -> path -> path -> Prop :=
| tpr_path: forall G p q U bs,
    G ⊢! p: {{ q }} ⪼ {{ q }} ->
    G ⊢!! q : U ->
    typed_path_repl_comp_qp G (q •• bs) (p •• bs).

Definition repl_composition_qp_p G := star (typed_path_repl_comp_qp G).

Notation "G '⊢' p '⟿'' q" := (repl_composition_qp_p G q p) (at level 40, p at level 59).

Notation "G '⊩' T '⟿' U '⬳' V" := (G ⊢ T ⟿ U /\ G ⊢ V ⟿ U) (at level 40, T at level 59).

Notation "G '⊩' p '⟿'' q '⬳' r" := (G ⊢ p ⟿' q /\ G ⊢ r ⟿' q) (at level 40, p at level 59).
