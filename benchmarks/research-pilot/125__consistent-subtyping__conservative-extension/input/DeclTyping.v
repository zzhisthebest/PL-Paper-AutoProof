Set Implicit Arguments.

Require Import TLC.LibLN.

Implicit Types x : var.

Require Import DeclDef DeclInfra DeclProp.

Inductive dtyping' : denv -> dtrm -> dtyp -> Prop :=
  | dtyping'_var : forall E x T,
      dokt E ->
      binds x (dbind_typ T) E ->
      dtyping' E (dtrm_fvar x) T
  | dtyping'_nat : forall E i,
      dokt E ->
      dtyping' E (dtrm_nat i) (dtyp_nat)
  | dtyping'_absann : forall x E A B e,
      dwft empty A ->
      x \notin (dom E \u dfv_ee e) ->
      dtyping' (E & x ~: A) (e dopen_ee_var x) B ->
      dtyping' E (dtrm_absann A e) (dtyp_arrow A B)
  | dtyping'_app : forall E e1 e2 A A1 A2 A3,
      dtyping' E e1 A ->
      dmatch E A A1 A2 ->
      dtyping' E e2 A3 ->
      dconsub E A3 A1 ->
      dtyping' E (dtrm_app e1 e2) A2
  | dtyping'_abs : forall x E A B e,
      x \notin (dom E \u dfv_ee e) ->
      dtyp_mono A ->
      dtyping' (E & x ~: A) (e dopen_ee_var x) B ->
      dtyping' E (dtrm_abs e) (dtyp_arrow A B)
  | dtyping'_gen : forall a E A e,
      a \notin (dom E \u dfv_tt A) ->
      dtyping' (E & a ~tvar) e (A dopen_tt_var a) ->
      dtyping' E e (dtyp_all A)
  | dtyping'_let : forall x E A B e1 e2,
      x \notin (dom E \u dfv_ee e2) ->
      dtyping' E e1 A ->
      dtyping' (E & x ~: A) (e2 dopen_ee_var x) B ->
      dtyping' E (dtrm_let e1 e2) B
.
