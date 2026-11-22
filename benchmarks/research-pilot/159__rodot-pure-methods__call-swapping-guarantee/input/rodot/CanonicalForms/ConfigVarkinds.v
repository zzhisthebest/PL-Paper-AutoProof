Set Implicit Arguments.

Require Import Coq.Program.Equality.

Require Import LibExtra.

Require Import AbstractSyntax TypingMode GeneralTyping EnvCorrespondence TFree Deref.

Inductive def_varkinds: ctx -> def -> Prop :=

| def_varkinds_fld G x l:
  ctx_k G x v_loc ->
  def_varkinds G (def_fld l (avar_f x))

| def_varkinds_typ G T l:
  def_varkinds G (def_typ l T)

| def_varkinds_met G t l:
  all_tfree_k G t v_ref ->
  def_varkinds G (def_met l t)
.

Inductive defs_varkinds: ctx -> defs -> Prop :=
| defs_varkinds_nil G:
  defs_varkinds G (defs_nil)
| defs_varkinds_cons G ds d:
  defs_varkinds G ds ->
  def_varkinds G d ->
  defs_varkinds G (defs_cons ds d)
.

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.
