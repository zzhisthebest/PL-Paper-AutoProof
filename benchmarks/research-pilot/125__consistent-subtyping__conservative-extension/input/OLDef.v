Require Import TLC.LibLN.

Require Import DeclDef DeclInfra DeclProp.

Inductive otyping : denv -> dtrm -> dtyp -> Prop :=
  | otyping_var : forall E x T,
      denv_static E ->
      binds x (dbind_typ T) E ->
      otyping E (dtrm_fvar x) T
  | otyping_nat : forall E i,
      denv_static E ->
      otyping E (dtrm_nat i) (dtyp_nat)
  | otyping_absann : forall L E A B e,
      dwft empty A ->
      (forall x, x \notin L ->
            otyping (E & x ~: A) (e dopen_ee_var x) B) ->
      otyping E (dtrm_absann A e) (dtyp_arrow A B)
  | otyping_abs : forall L E A B e,
      dtyp_mono A ->
      (forall x, x \notin L ->
            otyping (E & x ~: A) (e dopen_ee_var x) B) ->
      otyping E (dtrm_abs e) (dtyp_arrow A B)
  | otyping_app : forall E e1 e2 A1 A2,
      otyping E e1 (dtyp_arrow A1 A2) ->
      otyping E e2 A1 ->
      otyping E (dtrm_app e1 e2) A2
  | otyping_sub : forall E e A B,
      otyping E e A ->
      dsub E A B ->
      otyping E e B
  | otyping_gen : forall L E A e,
      (forall a, a \notin L ->
            otyping (E & a ~tvar) e (A dopen_tt_var a)) ->
      otyping E e (dtyp_all A)
  | otyping_let : forall L E e1 e2 A B,
      otyping E e1 A ->
      (forall x, x \notin L ->
            otyping (E & x ~: A) (e2 dopen_ee_var x) B) ->
      otyping E (dtrm_let e1 e2) B
.
