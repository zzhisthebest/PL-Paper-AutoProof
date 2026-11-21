Set Implicit Arguments.

From TLC Require Import LibList.

From TLC Require Import LibLN.

Require Import DeclDef.

Require Import FDef.

Require Import FInfra.

Require Import DeclInfra.

Require Import TransGen.

Require Import TransSubtyping.

Inductive d2ftyping : denv -> dstack -> dtrm -> dtyp -> ftrm -> Prop :=
  | d2ftyping_var : forall E x T f T2 cs,
      dokt E ->
      binds x T E ->
      d2fsub (stack cs) T T2 f ->
      d2ftyping E cs (dtrm_fvar x) T2
                (ftrm_app f (ftrm_fvar x))
  | d2ftyping_nat : forall E i,
      dokt E ->
      d2ftyping E nil (dtrm_nat i) (dtyp_nat)
                (ftrm_nat i)
  | d2ftyping_absann : forall L E V e1 T1 s,
      dwft \{} V ->
      (forall x, x \notin L ->
            d2ftyping (E & x ~ V) nil (e1 dopen_ee_var x) T1 (s fopen_ee_var x)) ->
      d2ftyping E nil (dtrm_absann V e1) (dtyp_arrow V T1)
                (ftrm_absann V s)
  | d2ftyping_abs : forall L E t e1 T1 s,
      dtype t ->
      dmono t ->
      (forall x, x \notin L ->
            d2ftyping (E & x ~ t) nil (e1 dopen_ee_var x) T1 (s fopen_ee_var x)) ->
      d2ftyping E nil (dtrm_abs e1) (dtyp_arrow t T1)
                (ftrm_absann t s)

  | d2ftyping_absann_stack : forall L E V e1 T1 c cs f s,
      dwft \{} V ->
      d2fsub plain c V f ->
      (forall x, x \notin L ->
            d2ftyping (E & x ~ V) cs (e1 dopen_ee_var x) T1 (s fopen_ee_var x)) ->
      d2ftyping E (cons c cs) (dtrm_absann V e1) (dtyp_arrow c T1)
              (ftrm_absann c
                           (ftrm_app (ftrm_absann V s) (ftrm_app f (ftrm_bvar 0))))
  | d2ftyping_abs_stack : forall L E e1 T1 c cs s,
      (forall x, x \notin L ->
            d2ftyping (E & x ~ c) cs (e1 dopen_ee_var x) T1 (s fopen_ee_var x)) ->
      d2ftyping E (cons c cs) (dtrm_abs e1) (dtyp_arrow c T1) (ftrm_absann c s)
  | d2ftyping_app : forall T1 T3 E e1 e2 T2 cs s1 s2 s3,
      d2ftyping E nil e2 T2 s2 ->
      d2fgen E T2 s2 T3 s3 ->
      d2ftyping E (cons T3 cs) e1 (dtyp_arrow T3 T1) s1 ->
      d2ftyping E cs (dtrm_app e1 e2) T1 (ftrm_app s1 s3)

  | d2ftyping_pair : forall E e1 e2 T1 T2 s1 s2,
      d2ftyping E nil e1 T1 s1 ->
      d2ftyping E nil e2 T2 s2 ->
      d2ftyping E nil (dtrm_pair e1 e2) (dtyp_pair T1 T2) (ftrm_pair s1 s2)
  | d2ftyping_fst : forall E T cs f,
      dokt E ->
      d2fsub (stack cs) fst_typ T f ->
      d2ftyping E cs dtrm_fst T (ftrm_app f
                                          (ftrm_tabs (ftrm_tabs (ftrm_absann (dtyp_pair (dtyp_bvar 1) (dtyp_bvar 0))
                                                                             (ftrm_fst (ftrm_bvar 0))
                                          ))))
  | d2ftyping_snd : forall E T cs f,
      dokt E ->
      d2fsub (stack cs) snd_typ T f ->
      d2ftyping E cs dtrm_snd T (ftrm_app f
                                          (ftrm_tabs (ftrm_tabs (ftrm_absann (dtyp_pair (dtyp_bvar 1) (dtyp_bvar 0))
                                                                             (ftrm_snd (ftrm_bvar 0))
                                          ))))
.
