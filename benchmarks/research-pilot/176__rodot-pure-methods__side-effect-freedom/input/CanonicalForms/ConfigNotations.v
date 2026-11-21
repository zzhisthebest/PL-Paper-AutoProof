Set Implicit Arguments.

Require Import LibExtra AbstractSyntax.

Require Import InertContext Deref.

Notation ctx_nothing_fresh_in_config G c :=
  (ctx_dom G \c fv_config c /\ nothing_fresh_in_config G c ).

Notation ty_nothing_fresh_in_config G U c :=
  (ctx_nothing_fresh_in_config G c  /\ nothing_fresh_in_config U c ).

Notation has_null Lv := (exists null, null \in Lv).

Notation inert_G_for_item G w y T := (G § y / v_loc ~ T § w / v_ref ~ T).

Notation inert_G_for_obj G w y T S := (inert_G_for_item G w y (typ_objref T S)).

Notation item_obj_dereffed e w y ds := (item_obj (deref_defs (e & w ~ y) (open w ds))).

Notation heap_with_obj_dereffed s e w y ds := (s & y ~ item_obj_dereffed e w y ds).
