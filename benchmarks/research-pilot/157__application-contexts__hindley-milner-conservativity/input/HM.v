Set Implicit Arguments.

From TLC Require Import LibList.

From TLC Require Import LibLN.

Require Import DeclDef.

Implicit Types x : var.

Definition htyp := dtyp.

Definition htyp_nat := dtyp_nat.

Definition htyp_bvar := dtyp_bvar.

Definition htyp_fvar := dtyp_fvar.

Definition htyp_arrow := dtyp_arrow.

Definition htyp_all := dtyp_all.

Inductive htrm : Set :=
  | htrm_bvar   : nat -> htrm
  | htrm_fvar   : var -> htrm
  | htrm_nat    : nat -> htrm
  | htrm_abs    : htrm -> htrm
  | htrm_app    : htrm -> htrm -> htrm
  | htrm_let    : htrm -> htrm -> htrm
.

Definition hopen_tt_rec := dopen_tt_rec.

Definition hopen_tt T U := dopen_tt T U.

Fixpoint hopen_ee_rec (k : nat) (f : htrm) (e : htrm) {struct e} : htrm :=
  match e with
  | htrm_bvar i       => If k = i then f else (htrm_bvar i)
  | htrm_fvar x       => htrm_fvar x
  | htrm_nat i        => htrm_nat i
  | htrm_abs e1       => htrm_abs (hopen_ee_rec (S k) f e1)
  | htrm_app e1 e2    => htrm_app (hopen_ee_rec k f e1) (hopen_ee_rec k f e2)
  | htrm_let e1 e2    => htrm_let (hopen_ee_rec k f e1) (hopen_ee_rec (S k) f e2)
  end.

Definition hopen_ee t u := hopen_ee_rec 0 u t.

Notation "T 'hopen_tt_var' X" := (hopen_tt T (htyp_fvar X)) (at level 67).

Notation "t 'hopen_ee_var' x" := (hopen_ee t (htrm_fvar x)) (at level 67).

Definition htype := dtype.

Definition htype_nat := dtype_nat.

Definition htype_var := dtype_var.

Definition htype_arrow := dtype_arrow.

Definition htype_all := dtype_all.

Inductive hterm : htrm -> Prop :=
  | hterm_var : forall x,
      hterm (htrm_fvar x)
  | hterm_nat : forall i,
      hterm (htrm_nat i)
  | hterm_abs : forall L e1,
      (forall x, x \notin L -> hterm (e1 hopen_ee_var x)) ->
      hterm (htrm_abs e1)
  | hterm_app : forall e1 e2,
      hterm e1 ->
      hterm e2 ->
      hterm (htrm_app e1 e2)
  | hterm_let : forall L e1 e2,
      hterm e1 ->
      (forall x, x \notin L -> hterm (e2 hopen_ee_var x)) ->
      hterm (htrm_let e1 e2).

Inductive hbind := dbind.

Definition henv := denv.

Definition hokt := dokt.

Definition hokt_empty := dokt_empty.

Definition hokt_typ := dokt_typ.

Definition hmono := dmono.

Definition hgen := dgen.

Inductive hinst : dtyp -> dtyp -> Prop :=
  | hinst_empty : forall t,
      htype t ->
      (forall n, t <> dtyp_all n) ->
      hinst t t
  | hinst_step : forall t t2 x,
      x \notin dfv_tt t ->
      hinst (t dopen_tt_var x) t2 ->
      hinst (dtyp_all t) t2.

Inductive htyping : henv -> htrm -> dtyp -> Prop :=
  | htyping_var : forall E x T T2,
      hokt E ->
      binds x T E ->
      hinst T T2 ->
      htyping E (htrm_fvar x) T2
  | htyping_nat : forall E i,
      hokt E ->
      htyping E (htrm_nat i) (htyp_nat)
  | htyping_abs : forall L E t e1 T1,
      htype t ->
      hmono t ->
      (forall x, x \notin L ->
            htyping (E & x ~ t) (e1 hopen_ee_var x) T1) ->
      htyping E (htrm_abs e1) (htyp_arrow t T1)
  | htyping_app : forall T1 E e1 e2 T2,
      htyping E e2 T1 ->
      htyping E e1 (htyp_arrow T1 T2) ->
      htyping E (htrm_app e1 e2) T2
  | htyping_let : forall L E e1 e2 T1 T2 T3,
      htyping E e1 T1 ->
      hgen E T1 T3 ->
      (forall X, X \notin L -> htyping (E & X ~ T3) (e2 hopen_ee_var X) T2) ->
      htyping E (htrm_let e1 e2) T2.
