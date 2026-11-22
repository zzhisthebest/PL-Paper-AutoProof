Set Implicit Arguments.

Require Import LibExtra DotTactics AbstractSyntax Defs GeneralTyping TypingMode.

Require Import HeapUpdate HeapCorrespondence.

Inductive defs_valid : defs -> Prop :=
| defs_valid_nil:
    defs_valid defs_nil
| defs_valid_cons ds d:
    defs_valid ds ->
    defs_hasnt ds (label_of d) ->
    defs_valid (defs_cons ds d).

Inductive heap_valid: heap -> Prop :=
| heap_valid_empty: heap_valid empty
| heap_valid_push_fun s x f: heap_valid s -> heap_valid (s & x ~ item_fun (f))
| heap_valid_push_obj s x ds: heap_valid s -> defs_valid ds -> heap_valid (s & x ~ item_obj (ds)).

Section WithTypingMode.

Context (typing_mode: Mode).

End WithTypingMode.
