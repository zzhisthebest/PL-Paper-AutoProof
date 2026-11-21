Set Implicit Arguments.

Require Import LibExtra.

Require Import Coq.Program.Equality.

Require Import AbstractSyntax TypingMode GeneralTyping RecordTypes InertContext TFree TFreeTyping HeapCorrespondence ConfigVarkinds NothingFresh ConfigNotations.

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive ty_stack : ctx -> renv -> typ -> stack -> typ -> Prop :=
  | ty_stack_nil : forall G e T U,
      G⁏e ⊢ T <: U ->
      ty_stack G e T stack_nil U
  | ty_stack_let : forall L G e s t S T U,
      ty_stack G e T s U ->
      (forall x,
          x \notin L ->
          G § x / v_let ~ S ⁏e ⊢ open x t ∶ T) ->
      ty_stack G e S (stack_cons (frame_let t) s) U.

Inductive heap_closed: heap -> Prop :=
| heap_closed_empty: heap_closed empty
| heap_closed_push S x i:
    heap_closed S ->
    closed i ->
    heap_closed (S & x ~ i)
.

Inductive config_closed: config -> Prop:=
  config_sealed_cfg t s Sigma e Lv:
    closed t ->
    closed s ->
    heap_closed Sigma ->
    config_closed (t; s; Sigma; e; Lv).

Inductive ty_config : ctx -> config -> typ -> Prop :=
| ty_config_c : forall G e s Sigma Lv t T U,
    inert G ->
    heap_correspond G e Sigma ->
    ty_stack G e T s U ->
    all_tfree_k_stack G s v_ref ->
    G⁏e ⊢ t ∶ T ->
    all_tfree_k G t v_ref ->
    ty_nothing_fresh_in_config G U (t ; s ; Sigma ; e; Lv) ->
    has_null Lv ->
    sealed G ->
    config_closed (t; s; Sigma; e; Lv) ->
    closed U ->
    ty_config G (t; s; Sigma; e; Lv) U.

Inductive config_typd : config -> typ -> Prop :=
| config_typd_c : forall Gamma c U,
    ty_config Gamma c U ->
    config_typd c U.

Inductive config_hastyp : config -> Prop :=
| config_hastyp_c : forall Gamma c U,
    ty_config Gamma c U ->
    config_hastyp c.

Notation "'⊢' c '∶' T" := (config_typd c T) (at level 40, c at level 59).

Notation config_initial_mk_typ t T null := (t; stack_nil; empty; empty; \{ null } \u fv t \u fv T) (only parsing).

Inductive config_initial: trm -> config -> Prop :=
  config_initial_mk t Lv: config_initial t (t; stack_nil; empty; empty; Lv).

End WithTypingMode.

Notation "'⊢' c '∶' T" := (config_typd _ c T) (at level 40, c at level 59).

Arguments ty_config {typing_mode}.

Arguments ty_stack {typing_mode}.

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.
