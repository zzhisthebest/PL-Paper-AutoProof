Set Implicit Arguments.

Require Import TLC.LibLN.

Implicit Types x : var.

Require Import DeclDef DeclInfra.

Inductive dsub' : denv -> dtyp -> dtyp -> Prop :=
  | dsub'_nat : forall E,
      dokt E ->
      dsub' E dtyp_nat dtyp_nat
  | dsub'_var : forall E x,
      dokt E ->
      binds x dbind_tvar E ->
      dsub' E (dtyp_fvar x) (dtyp_fvar x)
  | dsub'_unknown : forall E,
      dokt E ->
      dsub' E dtyp_unknown dtyp_unknown
  | dsub'_fun : forall E A1 A2 B1 B2,
      dsub' E B1 A1 ->
      dsub' E A2 B2 ->
      dsub' E (dtyp_arrow A1 A2) (dtyp_arrow B1 B2)
  | dsub'_allL : forall E A B tau,
      dtyp_mono tau ->
      dwft E tau ->
      dsub' E (dopen_tt A tau) B ->
      dsub' E (dtyp_all A) B
  | dsub'_allR : forall x E A B,
      x \notin dom E \u dfv_tt A \u dfv_tt B ->

      dsub' (E & x ~tvar) A (B dopen_tt_var x) ->
      dsub' E A (dtyp_all B)
.

Inductive dsub_size : denv -> dtyp -> dtyp -> nat -> Prop :=
  |dsub_size_nat : forall E,
     dokt E ->
     dsub_size E dtyp_nat dtyp_nat 1
  |dsub_size_var : forall E x,
      dokt E ->
      binds x dbind_tvar E ->
     dsub_size E (dtyp_fvar x) (dtyp_fvar x) 1
  |dsub_size_unknown : forall E,
      dokt E ->
      dsub_size E dtyp_unknown dtyp_unknown 1
  |dsub_size_arrow : forall E A1 A2 B1 B2 n1 n2,
     dsub_size E B1 A1 n1 ->
     dsub_size E A2 B2 n2 ->
     dsub_size E (dtyp_arrow A1 A2) (dtyp_arrow B1 B2) (1 + n1 + n2)
  |dsub_size_allL : forall E A2 B2 tau n1,
     dtyp_mono tau ->
     dwft E tau ->
     dsub_size E (dopen_tt A2 tau) B2 n1 ->
     dsub_size E (dtyp_all A2) B2 (1 + n1)
  |dsub_size_allR : forall L E A2 B2 n1,
     (forall x, x \notin L ->
           dsub_size (E & x ~tvar) A2 (B2 dopen_tt_var x) n1) ->
     dsub_size E A2 (dtyp_all B2) (1 + n1)
.
