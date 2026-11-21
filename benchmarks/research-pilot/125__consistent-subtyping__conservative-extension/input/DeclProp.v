Set Implicit Arguments.

Require Import TLC.LibLN.

Require Import DeclDef.

Require Import DeclInfra.

Require Import DeclSub.

Inductive dtyp_unknown_like : dtyp -> Prop :=
  | dtyp_unknown_like_intro:
      dtyp_unknown_like dtyp_unknown
  | dtyp_unknown_like_all: forall x,
      dtyp_unknown_like x ->
      dtyp_unknown_like (dtyp_all x)
.

Inductive dtyp_static : dtyp -> Prop :=
  | dtyp_static_nat:
      dtyp_static dtyp_nat
  | dtyp_static_fvar: forall i,
      dtyp_static (dtyp_fvar i)
  | dtyp_static_arrow: forall A B,
      dtyp_static A ->
      dtyp_static B ->
      dtyp_static (dtyp_arrow A B)
  | dtyp_static_all: forall L A,
      (forall x, x \notin L -> dtyp_static (A dopen_tt_var x)) ->
      dtyp_static (dtyp_all A)
.

Inductive dterm_static : dtrm -> Prop :=
  | dterm_static_var: forall x,
      dterm_static (dtrm_fvar x)
  | dterm_static_nat : forall i,
      dterm_static (dtrm_nat i)
  | dterm_static_absann : forall L V e1,
      dtyp_static V ->
      (forall x, x \notin L -> dterm_static (e1 dopen_ee_var x)) ->
      dterm_static (dtrm_absann V e1)
  | dterm_static_abs : forall L e1,
      (forall x, x \notin L -> dterm_static (e1 dopen_ee_var x)) ->
      dterm_static (dtrm_abs e1)
  | dterm_static_app : forall e1 e2,
      dterm_static e1 ->
      dterm_static e2 ->
      dterm_static (dtrm_app e1 e2)
  | dterm_static_let : forall L e1 e2,
      dterm_static e1 ->
      (forall x, x \notin L -> dterm_static (e2 dopen_ee_var x)) ->
      dterm_static (dtrm_let e1 e2)
.

Inductive denv_static : denv -> Prop :=
  | denv_static_empty : denv_static empty
  | denv_static_typ : forall E x T,
      denv_static E ->
      dtyp_static T ->
      dwft E T ->
      x # E ->
      denv_static (E & x ~: T)
  | denv_static_tvar : forall E x,
      denv_static E ->
      x # E ->
      denv_static (E & x ~tvar)
.

Inductive dtyp_less_precise : dtyp -> dtyp -> Prop :=
  | dtyp_less_precise_unknown: forall A,
      dtype A ->
      dtyp_less_precise dtyp_unknown A
  | dtyp_less_precise_tvar: forall x,
      dtyp_less_precise (dtyp_fvar x) (dtyp_fvar x)
  | dtyp_less_precise_nat:
      dtyp_less_precise dtyp_nat dtyp_nat
  | dtyp_less_precise_arrow: forall A1 A2 B1 B2,
      dtyp_less_precise A1 B1 ->
      dtyp_less_precise A2 B2 ->
      dtyp_less_precise (dtyp_arrow A1 A2) (dtyp_arrow B1 B2)
  | dtyp_less_precise_all: forall L A1 A2,
      (forall x, x \notin L ->
            dtyp_less_precise (A1 dopen_tt_var x) (A2 dopen_tt_var x)) ->
      dtyp_less_precise (dtyp_all A1) (dtyp_all A2)
.

Inductive dtyp_less_precise' : dtyp -> dtyp -> Prop :=
  | dtyp_less_precise'_unknown: forall A,
      dtype A ->
      dtyp_less_precise' dtyp_unknown A
  | dtyp_less_precise'_tvar: forall x,
      dtyp_less_precise' (dtyp_fvar x) (dtyp_fvar x)
  | dtyp_less_precise'_nat:
      dtyp_less_precise' dtyp_nat dtyp_nat
  | dtyp_less_precise'_arrow: forall A1 A2 B1 B2,
      dtyp_less_precise' A1 B1 ->
      dtyp_less_precise' A2 B2 ->
      dtyp_less_precise' (dtyp_arrow A1 A2) (dtyp_arrow B1 B2)
  | dtyp_less_precise'_all: forall x A1 A2,
      x \notin dfv_tt A1 \u dfv_tt A2 ->
      dtyp_less_precise' (A1 dopen_tt_var x) (A2 dopen_tt_var x) ->
      dtyp_less_precise' (dtyp_all A1) (dtyp_all A2)
.

Inductive dterm_less_precise : dtrm -> dtrm -> Prop :=
  | dterm_less_precise_fvar : forall x,
      dterm_less_precise (dtrm_fvar x) (dtrm_fvar x)
  | dterm_less_precise_nat : forall i,
      dterm_less_precise (dtrm_nat i) (dtrm_nat i)
  | dterm_less_precise_absann: forall L e1 e2 A1 A2,
      dtyp_less_precise A1 A2 ->
      (forall x, x \notin L ->
      dterm_less_precise (e1 dopen_ee_var x)
                         (e2 dopen_ee_var x)) ->
      dterm_less_precise (dtrm_absann A1 e1) (dtrm_absann A2 e2)
  | dterm_less_precise_app : forall e1 e2 e3 e4,
      dterm_less_precise e1 e2 ->
      dterm_less_precise e3 e4 ->
      dterm_less_precise (dtrm_app e1 e3) (dtrm_app e2 e4)
  | dterm_less_precise_abs: forall L e1 e2,
      (forall x, x \notin L ->
      dterm_less_precise (e1 dopen_ee_var x)
                         (e2 dopen_ee_var x)) ->
      dterm_less_precise (dtrm_abs e1) (dtrm_abs e2)
  | dterm_less_precise_let : forall L e1 e2 e3 e4,
      dterm_less_precise e1 e2 ->
      (forall x, x \notin L ->
            dterm_less_precise (e3 dopen_ee_var x) (e4 dopen_ee_var x)) ->
      dterm_less_precise (dtrm_let e1 e3) (dtrm_let e2 e4)
.

Inductive dterm_less_precise' : dtrm -> dtrm -> Prop :=
  | dterm_less_precise'_fvar : forall x,
      dterm_less_precise' (dtrm_fvar x) (dtrm_fvar x)
  | dterm_less_precise'_nat : forall i,
      dterm_less_precise' (dtrm_nat i) (dtrm_nat i)
  | dterm_less_precise'_absann: forall x e1 e2 A1 A2,
      dtyp_less_precise A1 A2 ->
      x  \notin (dfv_ee e1 \u dfv_ee e2) ->
      dterm_less_precise' (e1 dopen_ee_var x)
                         (e2 dopen_ee_var x) ->
      dterm_less_precise' (dtrm_absann A1 e1) (dtrm_absann A2 e2)
  | dterm_less_precise'_abs: forall x e1 e2,
      x  \notin (dfv_ee e1 \u dfv_ee e2) ->
      dterm_less_precise' (e1 dopen_ee_var x)
                         (e2 dopen_ee_var x) ->
      dterm_less_precise' (dtrm_abs e1) (dtrm_abs e2)
  | dterm_less_precise'_app : forall e1 e2 e3 e4,
      dterm_less_precise' e1 e2 ->
      dterm_less_precise' e3 e4 ->
      dterm_less_precise' (dtrm_app e1 e3) (dtrm_app e2 e4)
  | dterm_less_precise'_let : forall x e1 e2 e3 e4,
      x  \notin (dfv_ee e1 \u dfv_ee e2 \u dfv_ee e3 \u dfv_ee e4) ->
      dterm_less_precise' e1 e2 ->
      dterm_less_precise' (e3 dopen_ee_var x) (e4 dopen_ee_var x) ->
      dterm_less_precise' (dtrm_let e1 e3) (dtrm_let e2 e4)
.

Inductive denv_less_precise : denv -> denv -> Prop :=
  | denv_less_precise_refl: forall E,
      dokt E ->
      denv_less_precise E E
  | denv_less_precise_typ: forall E F x A1 A2,
      denv_less_precise E F ->
      dtyp_less_precise A1 A2 ->
      x # E -> x # F ->
      dwft E A1 ->
      dwft F A2 ->
      denv_less_precise (E & x ~: A1) (F & x ~: A2)
  | denv_less_precise_tvar: forall E F x,
      denv_less_precise E F ->
      x # E -> x # F ->
      denv_less_precise (E & x ~tvar) (F & x ~tvar)
.
