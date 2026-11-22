Set Implicit Arguments.

Require Import LibExtra.

Require Import AbstractSyntax TypingMode GeneralTyping EnvCorrespondence TFree ConfigVarkinds Defs RecordDefs.

Inductive defs_update : defs -> fld_label -> var -> defs -> Prop :=
| defs_update_var : forall ds a t x,
    defs_update (defs_cons ds (def_fld a t)) a x (defs_cons ds (def_fld a (avar_f x)))
| defs_update_push : forall ds d a x ds',
    defs_update ds a x ds' ->
    label_of d <> (label_fld a) ->
    defs_update (defs_cons ds d) a x (defs_cons ds' d).

Definition heap_update (s : heap) (x : var) (a : fld_label) (y : var) (s' : heap) :=
  ok s /\
  ok s' /\
  (dom s) = (dom s') /\
  (forall z v, z <> x ->
          binds z v s ->
          binds z v s') /\
  exists ds ds', binds x (item_obj ds) s /\
              defs_update ds a y ds' /\
              binds x (item_obj ds') s'.

Require Import RecordTypes InertContext HeapCorrespondence.

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.
