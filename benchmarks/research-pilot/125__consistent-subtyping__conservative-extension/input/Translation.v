Set Implicit Arguments.

Require Import TLC.LibLN.

Require Import DeclDef.

Require Import PBCDef DeclInfra PBCInfra.

Require Import DeclProp.

Inductive d2ptyping : denv -> dtrm -> dtyp -> ptrm -> Prop :=
  | d2ptyping_var : forall E x T,
      dokt E ->
      binds x (dbind_typ T) E ->
      d2ptyping E (dtrm_fvar x) T (ptrm_fvar x)
  | d2ptyping_nat : forall E i,
      dokt E ->
      d2ptyping E (dtrm_nat i) (dtyp_nat) (ptrm_nat i)
  | d2ptyping_absann : forall L E A B e s,
      dwft empty A ->
      (forall x, x \notin L ->
            d2ptyping (E & x ~: A) (e dopen_ee_var x) B (s popen_ee_var x)) ->
      d2ptyping E (dtrm_absann A e) (dtyp_arrow A B) (ptrm_absann A s)
  | d2ptyping_app : forall E e1 e2 A A1 A2 A3 s1 s2,
      d2ptyping E e1 A s1 ->
      dmatch E A A1 A2 ->
      d2ptyping E e2 A3 s2 ->
      dconsub E A3 A1 ->
      d2ptyping E (dtrm_app e1 e2) A2
                  (ptrm_app (ptrm_cast A (dtyp_arrow A1 A2) s1)
                            (ptrm_cast A3 A1 s2))
  | d2ptyping_abs : forall L E A B e s,
      dtyp_mono A ->
      (forall x, x \notin L ->
            d2ptyping (E & x ~: A) (e dopen_ee_var x) B (s popen_ee_var x)) ->
      d2ptyping E (dtrm_abs e) (dtyp_arrow A B) (ptrm_absann A s)
  | d2ptyping_gen : forall L E A e s,
      (forall a, a \notin L ->
            d2ptyping (E & a ~tvar) e (A dopen_tt_var a) (s popen_te_var a)) ->
      d2ptyping E e (dtyp_all A) (ptrm_tabs s)
  | d2ptyping_let : forall L E A B e1 e2 s1 s2,
      d2ptyping E e1 A s1 ->
      (forall x, x \notin L ->
            d2ptyping (E & x ~: A) (e2 dopen_ee_var x) B (s2 popen_ee_var x)) ->
      d2ptyping E (dtrm_let e1 e2) B (ptrm_app (ptrm_absann A s2) s1)
.

Fixpoint dtyp_len (t: dtyp) : nat :=
  match t with
  | dtyp_nat => 1
  | dtyp_unknown => 1
  | dtyp_fvar _ => 1
  | dtyp_bvar _ => 1
  | dtyp_arrow t1 t2 =>
      1 + dtyp_len t1 + dtyp_len t2
  | dtyp_all t1 =>
    1 + dtyp_len t1
  end.

Inductive d2ptyping' : denv -> dtrm -> dtyp -> ptrm -> Prop :=
  | d2ptyping'_var : forall E x T,
      dokt E ->
      binds x (dbind_typ T) E ->
      d2ptyping' E (dtrm_fvar x) T (ptrm_fvar x)
  | d2ptyping'_nat : forall E i,
      dokt E ->
      d2ptyping' E (dtrm_nat i) (dtyp_nat) (ptrm_nat i)
  | d2ptyping'_absann : forall x E A B e s,
      dwft empty A ->
      x \notin (dom E \u dfv_ee e \u pfv_ee s) ->
      d2ptyping' (E & x ~: A) (e dopen_ee_var x) B (s popen_ee_var x) ->
      d2ptyping' E (dtrm_absann A e) (dtyp_arrow A B) (ptrm_absann A s)
  | d2ptyping'_app : forall E e1 e2 A A1 A2 A3 s1 s2,
      d2ptyping' E e1 A s1 ->
      dmatch E A A1 A2 ->
      d2ptyping' E e2 A3 s2 ->
      dconsub E A3 A1 ->
      d2ptyping' E (dtrm_app e1 e2) A2
                  (ptrm_app (ptrm_cast A (dtyp_arrow A1 A2) s1)
                            (ptrm_cast A3 A1 s2))
  | d2ptyping'_abs : forall x E A B e s,
      x \notin (dom E \u dfv_ee e \u pfv_ee s) ->
      dtyp_mono A ->
      d2ptyping' (E & x ~: A) (e dopen_ee_var x) B (s popen_ee_var x) ->
      d2ptyping' E (dtrm_abs e) (dtyp_arrow A B) (ptrm_absann A s)
  | d2ptyping'_gen : forall a E A e s,
      a \notin (dom E \u dfv_tt A \u pfv_te s) ->
      d2ptyping' (E & a ~tvar) e (A dopen_tt_var a) (s popen_te_var a) ->
      d2ptyping' E e (dtyp_all A) (ptrm_tabs s)
  | d2ptyping'_let : forall x E A B e1 e2 s1 s2,
      x \notin (dom E \u dfv_ee e2 \u pfv_ee s2) ->
      d2ptyping' E e1 A s1 ->
      d2ptyping' (E & x ~: A) (e2 dopen_ee_var x) B (s2 popen_ee_var x) ->
      d2ptyping' E (dtrm_let e1 e2) B (ptrm_app (ptrm_absann A s2) s1)
.
