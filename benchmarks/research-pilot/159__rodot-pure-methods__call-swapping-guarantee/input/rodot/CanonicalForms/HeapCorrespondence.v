Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import LibExtra.

Require Import AbstractSyntax TypingMode GeneralTyping EnvCorrespondence Visibility TFree ConfigVarkinds Deref HeapInstantiate Indep RecordTypes InertContext RecordDefs Equivalence ConfigNotations.

Section WithTypingMode.

Context (typing_mode: Mode).

Inductive ty_item_s : ctx -> renv -> heap -> var -> Prop :=

| ty_item_fun_s : forall G e s x S t L T,
    mode_has_fun typing_mode ->
    ctx_binds x (typ_fun S T) G ->
    binds x (item_fun t) s ->
    (forall x, x \notin L ->
      G § x / v_par ~ S ⁏e ⊢ open x t ∶ open x T) ->
    all_tfree_k G t v_ref ->
    ty_item_s G e s x
| ty_item_obj_s : forall G e s x U S ds T,
    ctx_binds x T G ->
    binds x (item_obj ds) s ->
    T = typ_objref U S ->
    G §§ (objctx_heap x U) ⁏e ⊢ ds ∶ (open x U) ->
    defs_varkinds G ds ->
    ty_item_s G e s x.

Definition heap_correspond (G : ctx) (e: renv) (s : heap) : Prop :=
  ctx_ok G /\
  ctx_weakens G /\
  ok s /\
  ok e /\
  ctx_kdom v_loc G = dom s /\
  ctx_kdom v_ref G = dom e /\
  renv_corr G e /\
  (forall x,
      x \in dom s ->
      ty_item_s G e s x).

End WithTypingMode.

Arguments heap_correspond {typing_mode}.

Notation inert_G_for_item G w y T := (G § y / v_loc ~ T § w / v_ref ~ T).

Notation inert_G_for_obj G w y T S := (inert_G_for_item G w y (typ_objref T S)).

Notation heap_prefix S1 S2 := (exists S1', S2 = concat S1 S1').
