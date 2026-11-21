Set Implicit Arguments.

From TLC Require Import LibList.

From TLC Require Import LibLN.

Require Import DeclDef.

Require Import FDef.

Require Import FInfra.

Require Import DeclInfra.

Require Import TransGen.

Inductive d2fsub :aenv -> dtyp -> dtyp -> ftrm -> Prop :=
  |d2fsub_nat :
     d2fsub plain dtyp_nat dtyp_nat
            (ftrm_absann ftyp_nat (ftrm_bvar 0))
  |d2fsub_tvar : forall X,
     d2fsub plain (dtyp_fvar X) (dtyp_fvar X)
            (ftrm_absann (ftyp_fvar X) (ftrm_bvar 0))
  |d2fsub_arrow : forall S1 S2 T1 T2 f1 f2,
     d2fsub plain T1 S1 f1 ->
     d2fsub plain S2 T2 f2 ->
     d2fsub plain (dtyp_arrow S1 S2) (dtyp_arrow T1 T2)
            (ftrm_absann (ftyp_arrow S1 S2)
                         (ftrm_absann T1
                                      (ftrm_app f2
                                                (ftrm_app (ftrm_bvar 1)
                                                          (ftrm_app f1 (ftrm_bvar 0))))))
  |d2fsub_alll1 : forall S2 T2 U f1,
     dtype U ->
     dmono U ->
     d2fsub plain (dopen_tt S2 U) T2 f1 ->
     d2fsub plain (dtyp_all S2) T2
            (ftrm_absann (dtyp_all S2)
                         (ftrm_app f1
                                   (ftrm_tapp (ftrm_bvar 0) U)))
  |d2fsub_allr : forall L S2 T2 f,
     (forall X, X \notin L ->
           d2fsub plain S2 (T2 dopen_tt_var X) (f fopen_te_var X )) ->
     d2fsub plain S2 (dtyp_all T2)
            (ftrm_absann S2
                         (ftrm_tabs (ftrm_app f
                                              (ftrm_bvar 0))))

  |d2fsub_empty : forall A,
      dtype A ->
      d2fsub (stack nil) A A
           (ftrm_absann A (ftrm_bvar 0))
  |d2fsub_alll2 : forall S2 T2 U c cs f1,
     dtype U ->
     dmono U ->
     d2fsub (stack (cons c cs)) (dopen_tt S2 U) T2 f1 ->
     d2fsub (stack (cons c cs)) (dtyp_all S2) T2
            (ftrm_absann (dtyp_all S2)
                         (ftrm_app f1
                                   (ftrm_tapp (ftrm_bvar 0) U)))
  |d2fsub_arrow_stack : forall S1 S2 T2 c cs f1 f2,
     d2fsub plain c S1 f1 ->
     d2fsub (stack cs) S2 T2 f2 ->
     d2fsub (stack (cons c cs)) (dtyp_arrow S1 S2) (dtyp_arrow c T2)
            (ftrm_absann (ftyp_arrow S1 S2)
                         (ftrm_absann c
                                      (ftrm_app f2
                                                (ftrm_app (ftrm_bvar 1)
                                                          (ftrm_app f1 (ftrm_bvar 0))))))


  |d2fsub_pair : forall T1 T2 T3 T4 f1 f2,
      d2fsub plain T1 T3 f1 ->
      d2fsub plain T2 T4 f2 ->
      d2fsub plain (dtyp_pair T1 T2) (dtyp_pair T3 T4)
           (ftrm_absann (ftyp_pair T1 T2)
                        (ftrm_pair (ftrm_app f1 (ftrm_fst (ftrm_bvar 0)))
                                   (ftrm_app f2 (ftrm_snd (ftrm_bvar 0)))
                        ))
.
