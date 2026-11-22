Set Implicit Arguments.

From TLC Require Import LibLN.

Require Import STLC_Ref_Definitions.

Fixpoint fv (t : trm) {struct t} : vars :=
  match t with
  | trm_bvar i    => \{}
  | trm_fvar x    => \{x}
  | trm_abs t1    => (fv t1)
  | trm_app t1 t2 => (fv t1) \u (fv t2)
  | trm_unit      => \{}
  | trm_int n     => \{}
  | trm_loc l     => \{}
  | trm_ref t1    => (fv t1)
  | trm_get t1    => (fv t1)
  | trm_set t1 t2 => (fv t1) \u (fv t2)
  | trm_rand t1   => (fv t1)
  end.

Fixpoint subst (z : var) (u : trm) (t : trm) {struct t} : trm :=
  match t with
  | trm_bvar i    => trm_bvar i
  | trm_fvar x    => If x = z then u else (trm_fvar x)
  | trm_abs t1    => trm_abs (subst z u t1)
  | trm_app t1 t2 => trm_app (subst z u t1) (subst z u t2)
  | trm_unit      => trm_unit
  | trm_int n     => trm_int n
  | trm_loc l     => trm_loc l
  | trm_ref t1    => trm_ref (subst z u t1)
  | trm_get t1    => trm_get (subst z u t1)
  | trm_set t1 t2 => trm_set (subst z u t1) (subst z u t2)
  | trm_rand t1   => trm_rand (subst z u t1)
  end.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).

Definition body t :=
  exists L, forall x, x \notin L -> term (t ^ x).
